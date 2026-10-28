-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W22_localized_onecut_parent_recurrence_q68
-- name    : OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:19:54.142789+00:00
-- url     : https://prove2.me/theorems/2be317d9-a35c-4009-9962-2aa2f8521608
-- title:
--   OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W22.localized_onecut_parent_recurrence` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedOneCutPropagation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedOneCutPropagation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W22`, with `open PiExponentJets.W28.LocalIntersection`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem localized_onecut_parent_recurrence_q68
--       (I Q : Ideal A) [Q.IsPrime] (x : A)
--       (hdim : ringKrullDim (Localization.AtPrime Q ⧸
--         I.map (algebraMap A (Localization.AtPrime Q))) = 1)
--       (hregular : Function.Injective
--         (quotientMul (I.map (algebraMap A (Localization.AtPrime Q)))
--           (algebraMap A (Localization.AtPrime Q) x))) :
--       Module.length (Localization.AtPrime Q)
--         (Localization.AtPrime Q ⧸ (I ⊔ Ideal.span {x}).map
--           (algebraMap A (Localization.AtPrime Q))) = globalParentCutSum I Q x
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentJets.W22.globalParentCutSum` and `OAI.PiExponentJets.W28.LocalIntersection.quotientMul` (definitions bundle `OAIQ068A010` of this split).
--
--   **Used by.** The proof of `OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedOneCutPropagation.lean (declaration OAI.PiExponentJets.W22.localized_onecut_parent_recurrence)

import Mathlib
import Definitions.Def_OAIQ068A010

section

attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W28.LocalIntersection
open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem localized_onecut_parent_recurrence_q68
    (I Q : Ideal A) [Q.IsPrime] (x : A)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap A (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (quotientMul (I.map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) x))) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (I ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q))) = globalParentCutSum I Q x := by
  sorry

end PiExponentJets.W22

end OAI
end
