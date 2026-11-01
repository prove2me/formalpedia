-- Prove2me | Theorems.Thm_OAI_JointDickman_characterPerron_estimate_jd
-- name    : OAI.JointDickman.characterPerron_estimate_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:23:36.822183+00:00
-- url     : https://prove2.me/theorems/bf43ce01-6e64-48ef-963e-8be3ebcaf9bb
-- title:
--   OAI.JointDickman.characterPerron_estimate_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.characterPerron_estimate` of [lean/OAI/NumberTheory/JointDickman/Analysis/CharacterPerronEstimate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/CharacterPerronEstimate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Complex Set`):
--
--   ```lean
--   theorem characterPerron_estimate_jd {z ε : ℝ}
--       (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
--       ∃ A C K : ℝ, 0 < A ∧ A ≤ 1/4 ∧ 0 < C ∧ 0 < K ∧
--         ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
--         ∀ L c T : ℝ, 0 ≤ L → 0 < c → c ≤ 1/2 → 3 < T →
--         let δ := characterContourWidth A ε q (2*T)
--         let B := K*(((q:ℝ)+2)*(T+2))^(1/4:ℝ)
--         ‖VerticalIntegral' (characterNormalizedPerron χ z L) c‖ ≤
--           C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) +
--           (1/(2*Real.pi))*((5*B*Real.exp (-(L*(δ/2))))*Real.pi +
--             2*((5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.characterContourWidth` and `OAI.JointDickman.characterNormalizedPerron` (definitions bundle `OAIQ083J001` of this split); `VerticalIntegral'` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.jointDickmanLaw_unconditional_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/CharacterPerronEstimate.lean (declaration OAI.JointDickman.characterPerron_estimate)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section

attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Complex Set

theorem characterPerron_estimate_jd {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A C K : ℝ, 0 < A ∧ A ≤ 1/4 ∧ 0 < C ∧ 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ L c T : ℝ, 0 ≤ L → 0 < c → c ≤ 1/2 → 3 < T →
      let δ := characterContourWidth A ε q (2*T)
      let B := K*(((q:ℝ)+2)*(T+2))^(1/4:ℝ)
      ‖VerticalIntegral' (characterNormalizedPerron χ z L) c‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) +
        (1/(2*Real.pi))*((5*B*Real.exp (-(L*(δ/2))))*Real.pi +
          2*((5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c))) := by
  sorry

end JointDickman

end OAI
end
