-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_sm_idem_of_eigen
-- name    : GlobalTheory.DRFil.sm_idem_of_eigen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:52.475044+00:00
-- url     : https://prove2.me/theorems/883c5225-21c6-45c1-97b6-30db6f04b67d
-- title:
--   DRFil: sm idem of eigen
-- statement:
--   The DRFil construction uses the sm idem of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L223-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L223-L227

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

theorem GlobalTheory.DRFil.sm_idem_of_eigen (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] F)
    (hx : ∀ c : K, mulR Qp F LL V (algebraMap K F c) x = τ c • x) : sm Qp F LL V (idem F τ) x = x := by sorry
