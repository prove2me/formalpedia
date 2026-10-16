-- Prove2me | Theorems.Thm_OAI_TreeEdit_FiniteFourier_sum_multiplier_period
-- name    : OAI.TreeEdit.FiniteFourier.sum_multiplier_period
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:05:43.868576+00:00
-- url     : https://prove2.me/theorems/2fdbd83c-419d-42ca-9774-200dab942f04
-- title:
--   The multiplier $|1-\chi|^2$ sums to $2n$ over a full period of a nontrivial character value
-- statement:
--   Let $A$ be a finite abelian group and $\chi : A \to \mathbb{C}$ an additive character, i.e. $\chi(0) = 1$ and $\chi(x+y) = \chi(x)\chi(y)$ for all $x, y \in A$. Let $v \in A$ and let $n$ be a natural number, and suppose that $\chi(v) \ne 1$ but $\chi(v)^n = 1$. Then
--
--   $$
--   \sum_{s=0}^{n-1} \big|1 - \chi\big((s+1)v\big)\big|^2 = 2n.
--   $$
--
--   Thus, when $\chi$ is nontrivial on $v$ and $\chi(v)$ is an $n$-th root of unity, the multiplier $|1-\chi(\cdot)|^2$ has average exactly $2$ over the multiples $v, 2v, \dots, nv$. This is used to detect characters that are nontrivial on a periodic shift: their spectral weight is bounded by the average energy over the multiples of that shift.
--
--   **Formalization Note** The summand is `multiplier` of the character at the $(s+1)$-fold multiple of $v$, and the sum runs over `Finset.range n`. For $n = 0$ both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteFourier.lean#L376-L389

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier

open OAI OAI.TreeEdit OAI.TreeEdit.FiniteFourier
universe u
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

theorem OAI.TreeEdit.FiniteFourier.sum_multiplier_period (χ : AddChar A ℂ) (v : A) (n : ℕ)
    (hne : χ v ≠ 1) (hper : (χ v) ^ n = 1) :
    ∑ s ∈ Finset.range n, multiplier χ ((s + 1) • v) = 2 * n := by sorry
