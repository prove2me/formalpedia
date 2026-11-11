-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_represented_fractional_height_ae_affine
-- name    : OAI.RieszRectifiability.represented_fractional_height_ae_affine
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:49.873197+00:00
-- url     : https://prove2.me/theorems/2607c1e2-12ec-415d-89ca-98536e637f3a
-- title:
--   OAI.RieszRectifiability.represented_fractional_height_ae_affine: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.represented_fractional_height_ae_affine` of [lean/OAI/Analysis/RieszRectifiability/Rigidity/AffineHeightRigidity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Rigidity/AffineHeightRigidity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory SchwartzMap Function`, `open scoped NNReal`):
--
--   ```lean
--   theorem represented_fractional_height_ae_affine (p : ℕ)
--       (w : Ambient (p + 1) → ℝ) (hw : LocallyIntegrable w)
--       (T : 𝓢'(Ambient (p + 1), ℂ))
--       (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
--       (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
--         (∫ x, w x • fractionalSchwartzTest p g x) = 0)
--       (htail : IntegrableOn (fun x => |w x| * inverseDistancePow (p + 1 + 2) 0 x)
--         (closedExterior 0 1)) :
--       ∃ c : ℝ, ∃ L : Ambient (p + 1) →L[ℝ] ℝ, ∀ᵐ x, w x = c + L x
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.closedExterior`, `OAI.RieszRectifiability.fractionalSchwartzTest` and `OAI.RieszRectifiability.inverseDistancePow` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proofs of `OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy` and `OAI.RieszRectifiability.exists_dyadic_source_excess_limit` of this split import it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Rigidity/AffineHeightRigidity.lean (declaration OAI.RieszRectifiability.represented_fractional_height_ae_affine)

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

open MeasureTheory SchwartzMap Function
open scoped NNReal

theorem represented_fractional_height_ae_affine (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (hw : LocallyIntegrable w)
    (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0)
    (htail : IntegrableOn (fun x => |w x| * inverseDistancePow (p + 1 + 2) 0 x)
      (closedExterior 0 1)) :
    ∃ c : ℝ, ∃ L : Ambient (p + 1) →L[ℝ] ℝ, ∀ᵐ x, w x = c + L x := by
  sorry

end

end RieszRectifiability

end OAI
end
