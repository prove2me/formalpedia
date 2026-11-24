-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_isPoly_Tm
-- name    : GlobalTheory.CompanionTheory.Inh.CharId.isPoly_Tm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:48:27.590076+00:00
-- url     : https://prove2.me/theorems/3f76beeb-dbe4-4f02-a87c-caeba4728561
-- title:
--   Char Id: is Poly Tm
-- statement:
--   The Char Id construction uses the is Poly Tm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L59-L66

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset TensorProduct Formalism.HermitianLatticeCounting.S8
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inh GlobalTheory.CompanionTheory.Inh.CharId
open Polynomial Formalism.REAL
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem GlobalTheory.CompanionTheory.Inh.CharId.isPoly_Tm {n : ℕ} (E : Fin n → Fin n → B) (c : ℂ) (a b : Fin n) :
    IsPolyFun (fun u => Tm E (u - c) a b) := by sorry
