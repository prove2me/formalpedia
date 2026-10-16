-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_residue_double_count
-- name    : OAI.ShortEgyptian.residue_double_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:37:58.944985+00:00
-- url     : https://prove2.me/theorems/c0bf132b-264b-4162-b635-b47301950f46
-- title:
--   Double counting residues against truncated divisor counts
-- statement:
--   For positive integers $v,u$ write $r(v,u)=u\lceil v/u\rceil-v$; this is the least integer $r\ge0$ with $u\mid v+r$, and $0\le r(v,u)<u$. For a real number $X$ and a positive integer $n$ let $\tau_X(n)$ be the number of divisors $d$ of $n$ with $d\le X$.
--
--   Let $I$ be a finite nonempty index set, let $H,K,B$ be finite sets of natural numbers, let $(N_i)_{i\in I}$ be positive integers, and let $X,Y,\rho$ be real numbers with $\rho>0$. Write $r_i(u)=r(N_i,u)$ and assume:
--
--   1. every $u\in H$ satisfies $0<u\le X$;
--   2. every $u\in H$ with $u\le Y$ belongs to $K$;
--   3. for every $u\in H$ and every $i\in I$, if $r_i(u)\le Y$ then $r_i(u)\in K$;
--   4. every $u\in H$ with $u\notin B$ and $u>Y$ satisfies $\#\{i\in I: r_i(u)\le Y\}\ge\rho\,|I|/2$.
--
--   Then
--
--   $$
--   |H|\le |B|+|K|+\frac{2}{\rho\,|I|}\sum_{i\in I}\sum_{v\in K}\tau_X(N_i+v).
--   $$
--
--   This is the combinatorial core of a descent argument. Elements of $H$ that are neither exceptional (in $B$) nor already small are sent, for a positive proportion of the shifts $N_i$, to residues in the smaller set $K$, and a given residue $v\in K$ can only come from divisors $u\le X$ of $N_i+v$. Hence $|H|$ is controlled by $|K|$ plus an average of truncated divisor counts over shifted copies of $K$, a quantity that divisor moment estimates can handle.
--
--   **Formalization Note** $r(v,u)$ is `residue v u (quotient v u)`, where `quotient v u` is the natural-number ceiling of the rational $v/u$ and `residue` uses truncated subtraction (harmless, since $u\lceil v/u\rceil\ge v$). $\tau_X(n)$ is `truncatedDivisorCount X n`. The set $B$ enters through its full cardinality, whether or not $B\subseteq H$; the index set is a type with `Fintype` and `Nonempty` instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DoubleCount.lean#L14-L80

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale

open OAI OAI.ShortEgyptian
universe uI
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.residue_double_count {I : Type uI} [Fintype I] [Nonempty I]
    (H K B : Finset ℕ) (N : I → ℕ) (hN : ∀ i, 0 < N i) (X Y ρ : ℝ) (hρ : 0 < ρ)
    (hH : ∀ u ∈ H, 0 < u ∧ (u:ℝ) ≤ X)
    (hsmall : ∀ u ∈ H, (u:ℝ) ≤ Y → u ∈ K)
    (hlift : ∀ u ∈ H, ∀ i, (residue (N i) u (quotient (N i) u):ℝ) ≤ Y →
      residue (N i) u (quotient (N i) u) ∈ K)
    (hgood : ∀ u ∈ H, u ∉ B → Y < (u:ℝ) →
      ρ*(Fintype.card I:ℝ)/2 ≤ ((univ.filter fun i =>
        (residue (N i) u (quotient (N i) u):ℝ) ≤ Y).card:ℝ)) :
    (H.card:ℝ) ≤ B.card+K.card+2/(ρ*Fintype.card I)*
      ∑ i, ∑ v ∈ K, (truncatedDivisorCount X (N i+v):ℝ) := by sorry
