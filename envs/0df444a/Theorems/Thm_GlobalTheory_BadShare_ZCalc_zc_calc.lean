-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_ZCalc_zc_calc
-- name    : GlobalTheory.BadShare.ZCalc.zc_calc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:00:26.200812+00:00
-- url     : https://prove2.me/theorems/8ebe94ea-19cb-4f87-866d-075c3461d296
-- title:
--   ZCalc: zc calc
-- statement:
--   The ZCalc construction uses the zc calc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralIdempotentIrreducibleCharacterProps.lean#L61-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralIdempotentIrreducibleCharacterProps.lean#L61-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.ZCalc
variable {G : Type} [Group G] [Fintype G]

theorem GlobalTheory.BadShare.ZCalc.zc_calc : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by sorry
