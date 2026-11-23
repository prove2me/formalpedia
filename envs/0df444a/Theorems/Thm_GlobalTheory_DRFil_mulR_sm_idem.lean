-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_mulR_sm_idem
-- name    : GlobalTheory.DRFil.mulR_sm_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:30.799445+00:00
-- url     : https://prove2.me/theorems/fe4f46ad-be75-48f0-a985-73706801c958
-- title:
--   DRFil: mul R sm idem
-- statement:
--   The DRFil construction uses the mul R sm idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L219-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L219-L221

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
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
variable {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL]
variable [FiniteDimensional Qp K] [CharZero Qp] (F : Type) [CommRing F] [Algebra Qp F] [Algebra K F]
  [IsScalarTower Qp K F]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
variable {F}

theorem GlobalTheory.DRFil.mulR_sm_idem (τ : K →ₐ[Qp] LL) (c : K) (x : V ⊗[Qp] F) :
    mulR Qp F LL V (algebraMap K F c) (sm Qp F LL V (idem F τ) x) = τ c • sm Qp F LL V (idem F τ) x := by sorry
