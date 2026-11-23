-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_const
-- name    : GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:15.702777+00:00
-- url     : https://prove2.me/theorems/a3cca747-5e18-43f2-9cba-80be403a17b9
-- title:
--   Is Poly Fun: const
-- statement:
--   The Is Poly Fun construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean#L24-L24

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

theorem GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.const (b : B) : IsPolyFun (fun _ => b) := by sorry
