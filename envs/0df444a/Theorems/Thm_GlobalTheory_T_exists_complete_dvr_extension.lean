-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_complete_dvr_extension
-- name    : GlobalTheory.T.exists_complete_dvr_extension
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:45.650007+00:00
-- url     : https://prove2.me/theorems/f465dfe3-c241-4e82-a00a-df6b94bf4c3e
-- title:
--   T: exists complete dvr extension
-- statement:
--   The T construction uses the exists complete dvr extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteDvrExtensionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteDvrExtensionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtension
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtensionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_complete_dvr_extension : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V], ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O), Function.Injective φ ∧ IsLocalHom φ := by sorry
