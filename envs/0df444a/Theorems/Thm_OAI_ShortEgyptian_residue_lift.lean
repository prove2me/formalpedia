-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_residue_lift
-- name    : OAI.ShortEgyptian.residue_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:35:35.894043+00:00
-- url     : https://prove2.me/theorems/9dc5c849-60dd-4675-b9f0-b15462445875
-- title:
--   One residue step lifts an Egyptian fraction expansion of the residue to one of $u/(MQ)$
-- statement:
--   For natural numbers $v$ and $u\ge1$ let $r(v,u)=u\lceil v/u\rceil-v\in\{0,1,\dots,u-1\}$ be the distance from $v$ up to the least multiple of $u$ that is at least $v$. Call a finite list $n_1,\dots,n_L$ of natural numbers an *expansion of length $L$* of a rational number $x$ if every $n_i\ge2$ and $x=\sum_{i=1}^L1/n_i$; repeated entries are allowed.
--
--   **Theorem.** Let $M,Q,Q',u,t,k$ be natural numbers with $M>0$, $Q>0$, $Q'>0$, $Q'\mid Q$, $0<u<MQ$, $t>0$ and $t\mid M$. If $r(Qt,u)/(MQ')$ has an expansion of length at most $k$, then $u/(MQ)$ has an expansion of length at most $k+1$:
--
--   $$\frac{r(Qt,u)}{MQ'}\ \text{has an expansion of length}\le k\quad\Longrightarrow\quad\frac{u}{MQ}\ \text{has an expansion of length}\le k+1 .$$
--
--   This is the basic reduction step of the construction of short Egyptian fraction expansions: at the cost of one unit fraction, the numerator $u$ is replaced by the residue $r(Qt,u)$, which is small when $Qt$ lies just below a multiple of $u$, and the multiplier $Q$ in the denominator may be replaced by any divisor $Q'$ of it. It is used with $Q,Q'$ the multipliers of two consecutive levels during the level-by-level descent, and with $Q=Q'=1$ in the terminal stage.
--
--   **Formalization Note** $r(v,u)$ is `residue v u (quotient v u)`, where `quotient v u` is the natural-number ceiling of $v/u$ and `residue v u z = u*z - v`. "Has an expansion of length at most $k$" is `∃ ns, IsUnitSum x ns ∧ ns.length ≤ k`, where `IsUnitSum x ns` means every entry of `ns` is at least $2$ and the sum of reciprocals, computed in $\mathbb{Q}$, equals $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/TerminalExpansion.lean#L51-L88

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

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.residue_lift {M Q Q' u t k : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hQ' : 0 < Q')
    (hQQ : Q' ∣ Q) (hu : 0 < u) (huM : u < M*Q) (ht : 0 < t) (htM : t ∣ M)
    (hr : ∃ ns, IsUnitSum ((residue (Q*t) u (quotient (Q*t) u):ℚ)/(M*Q')) ns ∧ ns.length ≤ k) :
    ∃ ns, IsUnitSum ((u:ℚ)/(M*Q)) ns ∧ ns.length ≤ k+1 := by sorry
