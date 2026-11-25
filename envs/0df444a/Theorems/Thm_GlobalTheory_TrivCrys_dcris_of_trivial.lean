-- Prove2me | Theorems.Thm_GlobalTheory_TrivCrys_dcris_of_trivial
-- name    : GlobalTheory.TrivCrys.dcris_of_trivial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:05.546787+00:00
-- url     : https://prove2.me/theorems/143cb539-0058-4c30-ac49-7e7c1728ec36
-- title:
--   Triv Crys: dcris of trivial
-- statement:
--   The Triv Crys construction uses the dcris of trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCrysLatOfTrivial.lean#L67-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCrysLatOfTrivial.lean#L67-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_KernelDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_NonGaloisSurvey_CrystallineCyclotomic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCrysLatOfTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB
open GlobalTheory GlobalTheory.TrivCrys
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
open PowerSeries
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem GlobalTheory.TrivCrys.dcris_of_trivial {V : Type} [AddCommGroup V] [Module Qp V]
    [Module LL V] [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by sorry
