-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_schwartz_fractional_equation_of_real_pairing
-- name    : OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:11.524775+00:00
-- url     : https://prove2.me/theorems/7d838b15-ac75-410e-ab7c-333124b3452f
-- title:
--   OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing` of [lean/OAI/Analysis/RieszRectifiability/Rigidity/FractionalEquationFromRealPairing.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Rigidity/FractionalEquationFromRealPairing.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Filter SchwartzMap`):
--
--   ```lean
--   theorem schwartz_fractional_equation_of_real_pairing (p : ℕ)
--       (a : Ambient (p + 1)) (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
--       (hw : ∀ R : ℝ, 0 < R → IntegrableOn w (ball a R) volume)
--       (htail : ∀ R : ℝ, 0 < R → IntegrableOn
--         (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y) (closedExterior a R) volume)
--       (henergy : ∀ R : ℝ, 0 < R → Integrable
--         (fun q : Ambient (p + 1) × Ambient (p + 1) => fractionalPairEnergy (p + 1) w q.1 q.2)
--         ((volume.restrict (ball a R)).prod (volume.restrict (ball a R))))
--       (hreal : ∀ φ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport φ → (∫ x, φ x) = 0 →
--         ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
--           heightPairingOn (p + 1) volume a (ball a R) w φ = 0)
--       (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ x, g x) = 0) :
--       (∫ x, w x • fractionalSchwartzTest p g x) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.closedExterior`, `OAI.RieszRectifiability.fractionalPairEnergy`, `OAI.RieszRectifiability.fractionalSchwartzTest`, `OAI.RieszRectifiability.heightPairingOn` and `OAI.RieszRectifiability.inverseDistancePow` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.exists_common_height_with_fractional_equation` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Rigidity/FractionalEquationFromRealPairing.lean (declaration OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing)

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter SchwartzMap

theorem schwartz_fractional_equation_of_real_pairing (p : ℕ)
    (a : Ambient (p + 1)) (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : ∀ R : ℝ, 0 < R → IntegrableOn w (ball a R) volume)
    (htail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y) (closedExterior a R) volume)
    (henergy : ∀ R : ℝ, 0 < R → Integrable
      (fun q : Ambient (p + 1) × Ambient (p + 1) => fractionalPairEnergy (p + 1) w q.1 q.2)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R))))
    (hreal : ∀ φ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport φ → (∫ x, φ x) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) volume a (ball a R) w φ = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ x, g x) = 0) :
    (∫ x, w x • fractionalSchwartzTest p g x) = 0 := by
  sorry

end

end RieszRectifiability

end OAI
end
