-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TensorMultiplication_mulTens_tmul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication.mulTens_tmul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:39.844817+00:00
-- url     : https://prove2.me/theorems/b264a0d0-5c8a-4e66-9905-f35769b27d70
-- title:
--   Tensor Multiplication: mul Tens tmul
-- statement:
--   The Tensor Multiplication construction uses the mul Tens tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/TensorMultiplication.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/TensorMultiplication.lean#L73-L75

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication.mulTens_tmul (v : V) (v' : V') (b b' : B) :
    mulTens Qp B LL V V' ((v ⊗ₜ[Qp] b) ⊗ₜ[LL] (v' ⊗ₜ[Qp] b')) = (v ⊗ₜ[LL] v') ⊗ₜ[Qp] (b * b') := by sorry
