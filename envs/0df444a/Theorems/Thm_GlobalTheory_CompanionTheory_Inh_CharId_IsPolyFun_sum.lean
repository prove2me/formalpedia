-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_sum
-- name    : GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:23.720912+00:00
-- url     : https://prove2.me/theorems/f785d749-bf18-4a5b-acfa-504b6e21c52a
-- title:
--   Is Poly Fun: sum
-- statement:
--   The Is Poly Fun construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L38-L43

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

theorem GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → B) (h : ∀ i, IsPolyFun (f i)) :
    IsPolyFun (fun u => ∑ i ∈ s, f i u) := by sorry
