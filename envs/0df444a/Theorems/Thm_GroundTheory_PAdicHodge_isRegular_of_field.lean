-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isRegular_of_field
-- name    : GroundTheory.PAdicHodge.isRegular_of_field
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:21.013563+00:00
-- url     : https://prove2.me/theorems/f397342c-648b-4c7a-958c-d14739a97dd2
-- title:
--   PAdic Hodge: is Regular of field
-- statement:
--   The PAdic Hodge construction uses the is Regular of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L13-L33

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F B : Type*) [Group G] [Field F] [Field B] [Algebra F B] [MulSemiringAction G B]

theorem GroundTheory.PAdicHodge.isRegular_of_field : IsRegular G F B := by sorry
