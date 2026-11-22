-- Prove2me | Theorems.Thm_IterationStep
-- name    : IterationStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:44:04.572816+00:00
-- url     : https://prove2.me/theorems/b24b93f7-cc45-4f93-8d57-cb1ff4503c13
-- title:
--   Iteration Step: Iteration Step
-- statement:
--   One guarded step of the paper's main iteration (paper lines 228-240), stated purely about
--   the fixed function `v` and the radii, with NO sequence of rescaled functions.
--
--   The paper carries a sequence `v_l(x) = v(R_l x) / R_l^sigma` and asks that each `v_l` be
--   `p`-harmonic in `B_1`, vanish at zero, and satisfy `‖v_l‖_{L^∞(B_1)} ≤ 1`.  Those three
--   conditions, and the continuation condition `|Dv_l(0)| ≤ delta`, are properties of `v` and the
--   single radius `R = R_l`, so the rescaled functions need not appear in the statement:
--
--   * `‖v_l‖_{L^∞(B_1)} ≤ 1`  becomes  `∀ y, ‖y‖ < R → |v y| ≤ R ^ sigma`;
--   * `v_l(0) = 0`  becomes  `v 0 = 0`;
--   * `|Dv_l(0)| ≤ delta`  becomes  `R ^ (1 - sigma) * ‖gradient v 0‖ ≤ delta`, because
--     `Dv_l(0) = R^(1-sigma) Dv(0)`.
--
--   The rescaling bookkeeping lives in the proof, through `PHarmNormalize` and `PHarmRestrict`, and
--   the step itself is `Scales`.  The conclusion is the paper's eq:discrete at the next scale: a new
--   radius `R'` carrying the same normalization, with `theta * R ≤ R' ≤ R / 4`.
--
--   `delta` and `theta` are produced before `v`, as the paper's are: `delta` is the one from
--   `Scales` and `theta` is the minimum of its finite set of radii.  The standing hypothesis
--   `|v| ≤ 1` on `B_1` is the paper's own assumption on `v` at line 226; it is what makes `v`
--   differentiable at the origin, via `FirstOrderEstimateInput`, so that `Dv(0)` is the genuine
--   gradient and the displayed identity for `Dv_l(0)` holds.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IterationStep.lean#L27-L148
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IterationStep.lean#L27-L148

import Definitions.Def_PHigherOrder_PHarmNormalize
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_Scales
import Definitions.Def_PHigherOrder_IterationStep
import Theorems.Thm_PHarmNormalize
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_Scales

set_option autoImplicit false

theorem IterationStep (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hL : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 4 ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ y ∈ Metric.ball (0 : Plane) 1, |v y| ≤ 1) → v 0 = 0 →
        ∀ R : ℝ, 0 < R → R ≤ 1 →
          (∀ y : Plane, ‖y‖ < R → |v y| ≤ R ^ ((k : ℝ) + β)) →
          R ^ (1 - ((k : ℝ) + β)) * ‖gradient v 0‖ ≤ δ →
          ∃ R' : ℝ, 0 < R' ∧ R' ≤ 1 ∧
            (∀ y : Plane, ‖y‖ < R' → |v y| ≤ R' ^ ((k : ℝ) + β)) ∧
            θ * R ≤ R' ∧ R' ≤ R / 4 := by sorry
