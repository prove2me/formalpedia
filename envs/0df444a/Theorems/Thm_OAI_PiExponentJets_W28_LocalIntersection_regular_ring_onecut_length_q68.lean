-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W28_LocalIntersection_regular_ring_onecut_length_q68
-- name    : OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:20:19.681837+00:00
-- url     : https://prove2.me/theorems/565c4e3c-e8c6-4b7a-99f5-6918c1260f4a
-- title:
--   OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionMinimalSum.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionMinimalSum.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W28.LocalIntersection`, with `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem regular_ring_onecut_length_q68 (x : A) (hx : x ∈ nonZeroDivisors A) :
--       Module.length A (A ⧸ Ideal.span {x}) =
--         minimalPrimeCutSum (⊥ : Ideal A) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentJets.W28.LocalIntersection.minimalPrimeCutSum` (definitions bundle `OAIQ068A010` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68` and `OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionMinimalSum.lean (declaration OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length)

import Mathlib
import Definitions.Def_OAIQ068A010

section

attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [IsLocalRing A]

theorem regular_ring_onecut_length_q68 (x : A) (hx : x ∈ nonZeroDivisors A) :
    Module.length A (A ⧸ Ideal.span {x}) =
      minimalPrimeCutSum (⊥ : Ideal A) x := by
  sorry

end PiExponentJets.W28.LocalIntersection

end OAI
end
