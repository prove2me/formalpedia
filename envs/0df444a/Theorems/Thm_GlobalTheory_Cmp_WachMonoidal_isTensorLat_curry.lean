-- Prove2me | Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_isTensorLat_curry
-- name    : GlobalTheory.Cmp.WachMonoidal.isTensorLat_curry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:24:51.276263+00:00
-- url     : https://prove2.me/theorems/78996600-4e2d-5619-827b-e4f23ae36814
-- title:
--   Wach Monoidal: is Tensor Lat curry
-- statement:
--   The Wach Monoidal construction uses the is Tensor Lat curry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L169-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L169-L177

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem GlobalTheory.Cmp.WachMonoidal.isTensorLat_curry {T T' T'' : LocLat G Qp LL O} (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T)
    (hm : UnitDualParts.IsTensorLat m) :
    TensorProduct.lift (TensorProduct.curry m.toLinearMap) = m.toLinearMap ∧
      TensorLatticeUnitPart.IsTensorLat (TensorProduct.curry m.toLinearMap) := by sorry
