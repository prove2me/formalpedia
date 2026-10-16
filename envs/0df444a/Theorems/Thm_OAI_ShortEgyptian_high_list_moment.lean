-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_high_list_moment
-- name    : OAI.ShortEgyptian.high_list_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:10:32.548974+00:00
-- url     : https://prove2.me/theorems/9efcc4d2-3fbe-4547-b2c9-f21bd8236e33
-- title:
--   Mean-square equidistribution of $lCt_i/u$ for a list of $2^m$ distinct integers over the moduli $u\le X$
-- statement:
--   Throughout, $e(x)=\exp(2\pi i x)$ for $x\in\mathbb{R}$, and for $r\in\mathbb{N}$ we use the explicit constants
--
--   $$
--   P(r)=2^r(2r+4),\qquad K(r)=\bigl(18\cdot 3^{r+3}\bigr)^4\,\bigl((r+2)!\bigr)^2\,2^{2r}.
--   $$
--
--   Let $A$ be a finite nonempty set, let $S,X$ be real numbers, let $D,m,C,l$ be natural numbers, and let $t\colon A\to\mathbb{N}$, $i\mapsto t_i$. Assume:
--
--   1. (the list) $t$ is injective, $|A|=2^m$, and $t_i\le e^{101S}$ for every $i\in A$;
--   2. (the scale) $S>0$, $\log S\ge 1$, $D\ge 1000$ and $100\le m\le S/\log S$;
--   3. (the constants) $P(3D)\le\log S$ and $K(3D)\cdot 32^{P(3D)}\le e^{S/4}$;
--   4. (the ranges) $e^{S}\le X\le e^{DS/4}$, $e^{DS}\le C\le e^{2DS}$ and $1\le l\le e^{m/2500}$.
--
--   Then, writing $u_0=\lfloor Xe^{-m/10000}\rfloor+1$,
--
--   $$
--   \sum_{u=u_0}^{\lfloor X\rfloor}\,\Bigl|\frac{1}{|A|}\sum_{i\in A}e\Bigl(\frac{l\,C\,t_i}{u}\Bigr)\Bigr|^2\;\le\;X\,e^{-m/100}.
--   $$
--
--   Each summand is at most $1$ and there are at most $X$ moduli, so the content of the theorem is the saving factor $e^{-m/100}$. For a list of $2^m$ distinct integers of size at most $e^{101S}$, multiplied by a huge integer $C$ and a small frequency $l$, the normalized exponential sums over the list are small in mean square across the window of moduli $u\in(Xe^{-m/10000},X]$. So for most such $u$ the residues of $Ct_i$ modulo $u$ show no bias at frequency $l$. This is the deterministic second-moment input for counting the moduli at which a list of prime products fails to be equidistributed, in the construction of short Egyptian fraction expansions.
--
--   **Formalization Note** $P$ and $K$ are `reciprocalPower` and `reciprocalConstantNat`, and $e(x)$ is `phase x`. The summation limits use the natural-number floor `⌊·⌋₊`; the hypotheses force $X>0$, so these are the usual floors and every modulus $u$ in the range is at least $1$. The inner sum is divided by `Fintype.card A` cast to $\mathbb{C}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DeterministicLists.lean#L129-L167

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

open OAI OAI.ShortEgyptian
universe uA
open scoped BigOperators
open Finset Filter

theorem OAI.ShortEgyptian.high_list_moment {A : Type uA} [Fintype A] [Nonempty A]
    (S X : ℝ) (D m C l : ℕ) (t : A → ℕ) (hinj : Function.Injective t)
    (hcard : Fintype.card A = 2^m) (ht : ∀ i, (t i:ℝ) ≤ Real.exp (101*S))
    (hS : 0 < S) (hlog : 1 ≤ Real.log S) (hD : 1000 ≤ D)
    (hm : (m:ℝ) ≤ S/Real.log S) (hm100 : 100 ≤ (m:ℝ))
    (hP : (reciprocalPower (3*D):ℝ) ≤ Real.log S)
    (hconst : (reciprocalConstantNat (3*D):ℝ)*32^reciprocalPower (3*D) ≤ Real.exp (S/4))
    (hX : Real.exp S ≤ X) (hXD : X ≤ Real.exp ((D:ℝ)/4*S))
    (hClo : Real.exp ((D:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(D:ℝ)*S))
    (hl : 1 ≤ l) (hlhi : (l:ℝ) ≤ Real.exp ((1/2500:ℝ)*m)) :
    (∑ u ∈ Icc (⌊X*Real.exp (-(1/10000:ℝ)*m)⌋₊+1) ⌊X⌋₊,
      ‖(∑ i, phase ((l:ℝ)*C*t i/u))/(Fintype.card A:ℂ)‖^2) ≤
      X*Real.exp (-(1/100:ℝ)*m) := by sorry
