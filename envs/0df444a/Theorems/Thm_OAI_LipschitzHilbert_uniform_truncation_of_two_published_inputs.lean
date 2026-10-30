-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_uniform_truncation_of_two_published_inputs
-- name    : OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:44:29.392355+00:00
-- url     : https://prove2.me/theorems/e25c2010-9a10-485d-b57c-e5b5a0b9c72e
-- title:
--   OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs` of [lean/OAI/Analysis/LipschitzHilbert/TwoInputMain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/TwoInputMain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert`, with `open MeasureTheory Set`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem uniform_truncation_of_two_published_inputs
--       (hVariation : LepingleInput) (hLL : LaceyLiInput) :
--       ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
--         0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
--         ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
--         ∀ f : SchwartzMap Plane ℂ,
--           eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LaceyLiInput` and `OAI.LipschitzHilbert.LepingleInput` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.DirectionPlane`, `OAI.LipschitzHilbert.Plane` and `OAI.LipschitzHilbert.shortTransform` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.uniform_truncation` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/TwoInputMain.lean (declaration OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem uniform_truncation_of_two_published_inputs
    (hVariation : LepingleInput) (hLL : LaceyLiInput) :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  sorry

end LipschitzHilbert

end

end OAI
end
