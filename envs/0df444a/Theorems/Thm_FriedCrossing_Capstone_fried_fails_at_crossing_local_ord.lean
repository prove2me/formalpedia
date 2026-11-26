-- Prove2me | Theorems.Thm_FriedCrossing_Capstone_fried_fails_at_crossing_local_ord
-- name    : FriedCrossing.Capstone.fried_fails_at_crossing_local_ord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:47:49.525259+00:00
-- url     : https://prove2.me/theorems/1b11d73e-cf66-5205-8d12-7755106859d2
-- title:
--   Capstone: fried fails at crossing local ord
-- statement:
--   `fried_fails_at_crossing_local` with the zero's arrival given as `LinearArrival`, only required
--   at crossings inside |τ| < δ, and (9/11) the ζ-order fact `zetaOrder c = 0` taken directly at each
--   crossing — the exactness quartet enters the argument ONLY through it.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L392-L426
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L392-L426

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Capstone
open TorsionCore OrderCount Crossing RateRatio TwinRate PureZeros

theorem FriedCrossing.Capstone.fried_fails_at_crossing_local_ord
    (s ds z R : ℝ → ℝ) (c : Fin 5 → ℕ) (r δ τR : ℝ)
    (hτR : τR ≠ 0) (hr : 0 < r)
    (hs0 : s 0 < 0) (hsmall : |s 0| < r * δ)
    (hrate : ∀ τ, |τ| < δ → HasDerivAt s (ds τ) τ ∧ r ≤ ds τ)
    (hzero : ∀ τ₀, |τ₀| < δ → s τ₀ = 0 → ∃ a : ℝ, a ≠ 0 ∧ a ≠ ds τ₀ ∧ LinearArrival z a τ₀)
    (hcont : ∀ τ₀, s τ₀ = 0 → ContinuousAt R τ₀)
    (hfried_off : ∀ τ, |τ| < δ → s τ ≠ 0 → R τ * z τ / s τ = τR)
    (hord : ∀ τ₀, |τ₀| < δ → s τ₀ = 0 → zetaOrder c = 0) :
    ∃ σ, 0 < σ ∧ σ ≤ |s 0| / r ∧ σ < δ ∧ s σ = 0 ∧ (∀ τ, |τ| < δ → s τ = 0 → τ = σ) ∧
      zetaOrder c = 0 ∧
      ∃ a ratio : ℝ, a ≠ 0 ∧ ds σ ≠ 0 ∧
        Tendsto (fun τ => s τ / z τ) (𝓝[≠] σ) (𝓝 ratio) ∧
        ratio = ds σ / a ∧ ratio ≠ 1 ∧ R σ = τR * ratio ∧ R σ ≠ τR ∧
        refinedTorsion 1 (ds σ / (a - ds σ)) = -(a / ds σ) := by sorry
