-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_eq_zero_of_eval
-- name    : GlobalTheory.CompanionTheory.Inh.CharId.eq_zero_of_eval
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:48:22.40016+00:00
-- url     : https://prove2.me/theorems/6d81e1af-1737-4ab6-a5dd-e816b9c8d763
-- title:
--   Char Id: eq zero of eval
-- statement:
--   The Char Id construction uses the eq zero of eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L77-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L77-L95

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

theorem GlobalTheory.CompanionTheory.Inh.CharId.eq_zero_of_eval (P : B[X]) (h : ∀ u : ℂ, P.eval (algebraMap ℂ B u) = 0) : P = 0 := by sorry
