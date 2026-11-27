-- Prove2me | Theorems.Thm_GroundTheory_LocalField_maximalAbelianExtension_eq_iSup
-- name    : GroundTheory.LocalField.maximalAbelianExtension_eq_iSup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:34.051189+00:00
-- url     : https://prove2.me/theorems/b7c36dd8-d760-4d80-a0c8-4e1d093fa82d
-- title:
--   Local Field: maximal Abelian Extension eq i Sup
-- statement:
--   The Local Field construction uses the maximal Abelian Extension eq i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L155-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L155-L163

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

theorem GroundTheory.LocalField.maximalAbelianExtension_eq_iSup :
    maximalAbelianExtension F Ω =
      ⨆ (L : IntermediateField F Ω) (_ : FiniteDimensional F L) (_ : IsAbelianGalois F L), L := by sorry
