-- Prove2me | Theorems.Thm_KStar_Choice_isDiv_complex_circle
-- name    : KStar.Choice.isDiv_complex_circle
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:07.714811+00:00
-- url     : https://prove2.me/theorems/ba0f67cc-132a-4c81-bee7-d8f4513c46a6
-- title:
--   Choice: is Div complex circle
-- statement:
--   The Choice construction uses the is Div complex circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/HeckeCharacterChoice/ExtAlg.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/HeckeCharacterChoice/ExtAlg.lean#L8-L20

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_ExtAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Choice

theorem KStar.Choice.isDiv_complex_circle : IsDiv ℂˣ ∧ IsDiv Circle := by sorry
