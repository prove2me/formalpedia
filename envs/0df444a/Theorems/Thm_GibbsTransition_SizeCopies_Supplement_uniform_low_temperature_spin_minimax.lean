-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_uniform_low_temperature_spin_minimax
-- name    : GibbsTransition.SizeCopies.Supplement.uniform_low_temperature_spin_minimax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:44:43.261904+00:00
-- url     : https://prove2.me/theorems/56aa30e5-4eb4-4d5c-b6e7-f2fb6ac1e0f3
-- title:
--   Theorem 5.4 — Uniform low-temperature spin minimax
-- statement:
--   There are absolute positive constants $c,C$, independent of accuracy and inverse temperature, such that for every rational $0<\epsilon\le1/16$ and $\beta\ge512/\epsilon$,
--   $$c\epsilon^{-3}\le V_\beta^*(\epsilon)\le C\epsilon^{-3}.$$
--   The minimax value is the actual infimum over all correct, almost-surely stopping Gibbs learners at confidence $9/10$ of their worst-case expected supplied-spin count. Infinite expectations are allowed. The specified local upper learner also has side at most $C_s/\epsilon$, at most $C_n\log^2(1/\epsilon)$ copies, and at most $C\epsilon^{-3}$ supplied spins, with all constants fixed before both inputs and the unknown instance.
--
--   The source proof permits the lower witness $c=(2/5)\kappa^3$. Its upper schedule works over the entire stated temperature range, not just its boundary.
--
--   Differences from the source:
--   - encoding: minimax expected spin bounds and big-O upper resources → ENNReal infimum/supremum and uniform constants for the explicit deterministic schedule; reason: infimum of the empty learner class is infinity; scheduled path costs also bound expectations
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem 5.4, printed p. 12 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_LowTemperature
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem uniform_low_temperature_spin_minimax :
    ∃ c C Cs Cn : ℝ, 0 < c ∧ 0 < C ∧ 0 < Cs ∧ 0 < Cn ∧
    ∀ epsilon beta : ℚ, 0 < epsilon → epsilon ≤ 1/16 → 512/epsilon ≤ beta →
      ENNReal.ofReal (c*(epsilon : ℝ)⁻¹^3) ≤ spinMinimax beta epsilon ∧
      spinMinimax beta epsilon ≤ ENNReal.ofReal (C*(epsilon : ℝ)⁻¹^3) ∧
      (groundCopies starData epsilon (1/10) : ℝ) ≤ Cn*(Real.log (1/(epsilon : ℝ)))^2 ∧
      (largeGibbsSpins epsilon (1/10) : ℝ) ≤ C*(epsilon : ℝ)⁻¹^3 ∧
      (∀ k < groundRounds epsilon, (largeGibbsSide k : ℝ) ≤ Cs/(epsilon : ℝ)) ∧
      ∀ u : Interaction, InClass u →
        LawCorrect (largeGibbsFinal u beta epsilon (1/10)) (transitionPoint u) epsilon (1/10) := by sorry

end GibbsTransition.SizeCopies.Supplement
