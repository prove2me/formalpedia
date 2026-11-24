-- Prove2me | Theorems.Thm_GlobalTheory_Div_QFibre_exists_emb
-- name    : GlobalTheory.Div.QFibre.exists_emb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:50:51.11913+00:00
-- url     : https://prove2.me/theorems/abced57c-df22-4328-a5f1-5169a89d7a2e
-- title:
--   QFibre: exists emb
-- statement:
--   The QFibre construction uses the exists emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivFourierClassesPosConeSummand.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivFourierClassesPosConeSummand.lean#L43-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.QFibre
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.Div.QFibre.exists_emb [IsTotallyReal F] : Nonempty (Emb F) := by sorry
