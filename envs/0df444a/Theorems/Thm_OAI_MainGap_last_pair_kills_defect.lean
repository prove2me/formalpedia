-- Prove2me | Theorems.Thm_OAI_MainGap_last_pair_kills_defect
-- name    : OAI.MainGap.last_pair_kills_defect
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:23:33.582992+00:00
-- url     : https://prove2.me/theorems/d401c2f0-6911-4e1f-99a8-91b8e01a2713
-- title:
--   An orthogonal pair with equal moduli under a scalar eigen-relation forces $P=0$
-- statement:
--   Let $A$ be a unital C*-algebra.
--
--   **Theorem.** Let $P,B_3,B_4\in A$ and let $h\in\mathbb{R}$ with $h\neq0$. Suppose
--
--   $$
--   PB_4=B_4,\qquad B_3^*B_4=0,\qquad B_3^*B_3=B_4^*B_4,\qquad (B_3B_3^*)\,P=h\,P.
--   $$
--
--   Then $P=0$.
--
--   This is the algebraic core of a contradiction argument: if $B_3B_3^*$ acts on a nonzero element $P$ as a nonzero scalar while $B_4$ is fixed by $P$, then $B_3$ and $B_4$ cannot have orthogonal ranges and equal moduli. It is applied with $h=\tfrac12$ and $P$ a nonzero projection to rule out a configuration of four chosen elements.
--
--   **Formalization Note** The scalar $h$ acts by real scalar multiplication `h • P`. The unit of $A$ and the order on $A$ play no role in the statement or proof (the order instance is omitted for this lemma).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/ChoicePairs.lean#L227-L242

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem OAI.MainGap.last_pair_kills_defect {P B₃ B₄ : A} {h : ℝ} (hh : h ≠ 0)
    (hPB₄ : P * B₄ = B₄) (hcross : star B₃ * B₄ = 0)
    (hmod : star B₃ * B₃ = star B₄ * B₄)
    (hD : (B₃ * star B₃) * P = h • P) : P = 0 := by sorry
