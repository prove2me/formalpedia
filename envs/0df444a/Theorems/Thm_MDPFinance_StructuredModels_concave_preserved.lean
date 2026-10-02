-- Prove2me | Theorems.Thm_MDPFinance_StructuredModels_concave_preserved
-- name    : MDPFinance.StructuredModels.concave_preserved
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:36:45.025979+00:00
-- url     : https://prove2.me/theorems/f4ea04ff-a6ad-4232-a86d-c3220bf6c8ce
-- title:
--   Proposition 2.4.18 — $T_n$ preserves concavity
-- statement:
--   Let $v \in \mathbb{I\!B}_b^+$ and suppose (i) $D_n$ is convex in $E \times A$; (ii) $(x,a)
--   \mapsto L_n v(x,a)$ is concave on $D_n$. Then $T_n v$ is concave on $E$.
--
--   **Formalization Note.** Uses `ConcaveOnEReal`, this mission's `EReal`-valued analogue of
--   Mathlib's `ConcaveOn` (see the `ConcaveOnEReal` definition item).
--
--   **Formalization Note (moderation).** $v \in \mathbb{I\!B}_b^+$ for a model with upper
--   bounding function $b$, and $n < N$, as in the book's standing setting.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 36, Proposition 2.4.18

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Proposition 2.4.18 (Bäuerle–Rieder, p. 36, PDF 51). Let `v ∈ IB_b^+` and suppose the
following assumptions are satisfied: (i) `D_n` is convex in `E × A`; (ii) `L_n v(x,a)` is concave
on `D_n`. Then `T_n v` is concave on `E`. -/
theorem concave_preserved {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hD_convex : Convex ℝ (M.D n))
    (hL_concave : ConcaveOnEReal (M.D n) (L M n v)) :
    ConcaveOnEReal Set.univ (T M n v) := by sorry

end MDPFinance.StructuredModels
