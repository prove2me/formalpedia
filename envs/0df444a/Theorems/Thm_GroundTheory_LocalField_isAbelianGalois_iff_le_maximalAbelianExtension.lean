-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isAbelianGalois_iff_le_maximalAbelianExtension
-- name    : GroundTheory.LocalField.isAbelianGalois_iff_le_maximalAbelianExtension
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:03.293066+00:00
-- url     : https://prove2.me/theorems/ad7d8825-dafd-4460-818e-f6317a8413a7
-- title:
--   Local Field: is Abelian Galois iff le maximal Abelian Extension
-- statement:
--   The Local Field construction uses the is Abelian Galois iff le maximal Abelian Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L255-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L255-L257

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem GroundTheory.LocalField.isAbelianGalois_iff_le_maximalAbelianExtension (E : IntermediateField F Ω) [Normal F E] :
    IsAbelianGalois F E ↔ E ≤ maximalAbelianExtension F Ω := by sorry
