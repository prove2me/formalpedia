-- Prove2me | Theorems.Thm_OAI_JointDickman_primeRampProfile_from_published_jd
-- name    : OAI.JointDickman.primeRampProfile_from_published_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:33:40.555245+00:00
-- url     : https://prove2.me/theorems/632f65ed-128e-421f-aff3-40bac2bf91fa
-- title:
--   OAI.JointDickman.primeRampProfile_from_published_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.primeRampProfile_from_published` of [lean/OAI/NumberTheory/JointDickman/Amplification/PublishedRampProfile.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/PublishedRampProfile.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Filter MeasureTheory`, `open scoped Topology NNReal`, `open Classical in`):
--
--   ```lean
--   theorem primeRampProfile_from_published_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput) :
--       ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧
--         ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ lo hi : ℝ, 0 < lo → lo < hi →
--         ∃ M L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
--           (∀ x, |rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi x| ≤ M) ∧
--           LipschitzWith L (rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi) ∧
--           ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
--           ∀ lower upper : D → ℝ,
--           (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
--           (∀ d, lower d < upper d) → (∀ d, upper d ≤ 16 / 5) →
--           ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
--           |primeRampCell B q lower upper lo hi c (d, r) -
--             (∫ x in lower d..upper d,
--               rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi
--                 (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)) / q.totient| ≤
--             C * (B : ℝ) ^ (-(80 : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.primeRampCell`, `OAI.JointDickman.rampDensity`, `OAI.JointDickman.retainedPrimeProduct`, `OAI.JointDickman.squarefreeLeadingConstant`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.scaledRoughDensity` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.bounded_box_coarse_comparison_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/PublishedRampProfile.lean (declaration OAI.JointDickman.primeRampProfile_from_published)

import Mathlib
import Definitions.Def_OAIQ083J003

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman

open Filter MeasureTheory
open scoped Topology NNReal

open Classical in
theorem primeRampProfile_from_published_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ lo hi : ℝ, 0 < lo → lo < hi →
      ∃ M L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
        (∀ x, |rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi x| ≤ M) ∧
        LipschitzWith L (rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi) ∧
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, lower d < upper d) → (∀ d, upper d ≤ 16 / 5) →
        ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |primeRampCell B q lower upper lo hi c (d, r) -
          (∫ x in lower d..upper d,
            rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi
              (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  sorry

end JointDickman

end OAI
end
