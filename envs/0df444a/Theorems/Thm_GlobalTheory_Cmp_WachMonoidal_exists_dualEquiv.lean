-- Prove2me | Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_exists_dualEquiv
-- name    : GlobalTheory.Cmp.WachMonoidal.exists_dualEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:26:18.659366+00:00
-- url     : https://prove2.me/theorems/2aeb4753-9455-496e-9296-2d2fde2f358a
-- title:
--   Wach Monoidal: exists dual Equiv
-- statement:
--   The Wach Monoidal construction uses the exists dual Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L359-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L359-L390

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
variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem GlobalTheory.Cmp.WachMonoidal.exists_dualEquiv {A R D D' : Type} [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup D] [Module R D] [Module A D] [IsScalarTower A R D]
    [AddCommGroup D'] [Module R D'] [Module A D'] [IsScalarTower A R D']
    (hinj : Function.Injective (algebraMap A R)) (N : Submodule A D) (N' : Submodule A D')
    (b : D →ₗ[R] D' →ₗ[R] R) (hv : ∀ y ∈ N', ∀ x ∈ N, ∃ a : A, b x y = algebraMap A R a)
    (hi : ∀ y, (∀ x ∈ N, b x y = 0) → y = 0)
    (hs : ∀ f : ↥N →ₗ[A] A, ∃ y ∈ N', ∀ x : ↥N, b (x : D) y = algebraMap A R (f x)) :
    ∃ δ : ↥N' ≃ₗ[A] Module.Dual A ↥N,
      ∀ (x : ↥N) (y : ↥N'), b (x : D) (y : D') = algebraMap A R (δ y x) := by sorry
