-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_scalar
-- name    : GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.scalar
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:48:27.516552+00:00
-- url     : https://prove2.me/theorems/5bfacc27-0489-4e83-8e33-c9c1a2cf7e9d
-- title:
--   Is Poly Fun: scalar
-- statement:
--   The Is Poly Fun construction uses the scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L26-L26

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

theorem GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.scalar : IsPolyFun (fun u => algebraMap ℂ B u) := by sorry
