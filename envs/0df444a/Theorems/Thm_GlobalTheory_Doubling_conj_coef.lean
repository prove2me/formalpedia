-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_conj_coef
-- name    : GlobalTheory.Doubling.conj_coef
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:59.836228+00:00
-- url     : https://prove2.me/theorems/82df07f0-ec94-4e80-aa6d-d409f437d111
-- title:
--   Doubling: conj coef
-- statement:
--   The Doubling construction uses the conj coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L285-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L285-L286

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {H : Type} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

theorem GlobalTheory.Doubling.conj_coef (π : H → X → X) (x y : X) (g : H) : starRingEnd ℂ (coef π x y g) = inner ℂ (π g x) y := by sorry
