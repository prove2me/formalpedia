-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_prod_ofFn
-- name    : GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.prod_ofFn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:48:41.347636+00:00
-- url     : https://prove2.me/theorems/635fc104-033e-4af5-80a6-699784cf14f6
-- title:
--   Is Poly Fun: prod of Fn
-- statement:
--   The Is Poly Fun construction uses the prod of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L45-L49

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

theorem GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.prod_ofFn : ∀ (t : ℕ) (f : Fin t → ℂ → B), (∀ i, IsPolyFun (f i)) →
    IsPolyFun (fun u => (List.ofFn fun k => f k u).prod)
  := by sorry
