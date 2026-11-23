-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_tmul_eq_sm_bil
-- name    : GlobalTheory.DRFil.tmul_eq_sm_bil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:52.443899+00:00
-- url     : https://prove2.me/theorems/828add3a-b13c-44c2-846b-be087192ddb1
-- title:
--   DRFil: tmul eq sm bil
-- statement:
--   The DRFil construction uses the tmul eq sm bil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean#L53-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem GlobalTheory.DRFil.tmul_eq_sm_bil (E : V ⊗[LL] V' ≃ₗ[LL] V'') (v : V) (w : V') (b : F) :
    E (v ⊗ₜ[LL] w) ⊗ₜ[Qp] b = sm Qp F LL V'' ((1 : LL) ⊗ₜ[Qp] b)
      (bil Qp F (tensBil E) (v ⊗ₜ[Qp] (1 : F)) (w ⊗ₜ[Qp] (1 : F))) := by sorry
