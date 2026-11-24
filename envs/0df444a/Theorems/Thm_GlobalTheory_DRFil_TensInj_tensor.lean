-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_TensInj_tensor
-- name    : GlobalTheory.DRFil.TensInj.tensor
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:12:51.654817+00:00
-- url     : https://prove2.me/theorems/9561c07e-6f42-4bf0-b79d-9a35a5ca27b5
-- title:
--   Tens Inj: tensor
-- statement:
--   The Tens Inj construction uses the tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComponentEquiv.lean#L130-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComponentEquiv.lean#L130-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
import Theorems.Thm_GlobalTheory_DRFil_Adapted_tensor
import Theorems.Thm_GlobalTheory_DRFil_Spans_tensor

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
variable {PD}

theorem GlobalTheory.DRFil.TensInj.tensor (h : TensInj PD) (m : ℕ) (c : Fin m → K) (hc : LinearIndependent K₀ c)
    (x : Fin m → V ⊗[Qp] B)
    (hx : ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)) = 0) (i : Fin m) :
    x i = 0 := by sorry
