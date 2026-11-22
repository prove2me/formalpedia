-- Prove2me | Theorems.Thm_Main
-- name    : Main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:22:26.354163+00:00
-- url     : https://prove2.me/theorems/34fe0514-8642-49f4-b962-9d5e7ba404b5
-- title:
--   Main: Main
-- statement:
--   The paper's main theorem, `thm:main` (paper lines 108-113): for `1 < p < 2`, every integer
--   `k ≥ 2` and every `0 < beta < 1` with `k + beta < s(p)`, there is `C = C(p,k,beta) < ∞` such
--   that every `p`-harmonic `u ∈ L^p(B_1)` satisfies eq:main.
--
--   Two renderings separate this statement from eq:main as the paper writes it, and both are
--   discussed in the `.tex` statement, where the faithfulness argument belongs.  First, the
--   derivative terms are carried through DIAGONAL evaluations `D^j u(x)[w,…,w]`, homogeneous of
--   degree `j` in `w`, rather than through the operator norms `‖D^j u(x)‖`; that is the standing
--   interface of this development and it is forced by what Mathlib supplies.  Second, eq:main is
--   ONE inequality on a SUM of `k + 2` terms whereas the conclusion here is a conjunction of two
--   quantified FAMILIES of bounds; the two are interderivable with a factor depending only on `k`.
--   Both factors depend only on `k` and are absorbed by `C`, which the paper itself quantifies as
--   `C(p,k,beta)` at line 313.
--
--   The `j = 0` term of the paper's sum is the `L^∞` bound on `B_{1/2}` and needs no clause of its
--   own: at `j = 0` the diagonal evaluation is `u x` and `‖w‖ ^ 0 = 1`, so that case of the first
--   clause IS local boundedness, restricted from `B_{3/4}` to `B_{1/2}`, which is the ingredient
--   paper line 313 names alongside the derivative bounds.
--
--   `C` is produced BEFORE `u`, as a single maximum of the two suppliers' constants and the local
--   boundedness constant.  That quantifier order is the whole content of the theorem: it is the
--   uniformity the qualitative higher regularity of Iwaniec-Manfredi does not provide, and which
--   the compactness argument of section 2 is what supplies.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Main.lean#L28-L77
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Main.lean#L28-L77

import Definitions.Def_PHigherOrder_HolderFromJets
import Definitions.Def_PHigherOrder_JetBounds
import Definitions.Def_PHigherOrder_LocalBoundednessInput
import Definitions.Def_PHigherOrder_Main
import Theorems.Thm_HolderFromJets
import Theorems.Thm_JetBounds

set_option autoImplicit false

theorem Main (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (hLB : LocalBoundednessInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
        MeasureTheory.MemLp u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
        (∀ j : ℕ, j ≤ k → ∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ w : Plane,
            |iteratedFDeriv ℝ j u x (fun _ => w)|
              ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                    (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                * ‖w‖ ^ j)
          ∧ (∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ y ∈ Metric.ball (0 : Plane) (1 / 2),
              ∀ w : Plane,
                |iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w)|
                  ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                    * ‖x - y‖ ^ β * ‖w‖ ^ k) := by sorry
