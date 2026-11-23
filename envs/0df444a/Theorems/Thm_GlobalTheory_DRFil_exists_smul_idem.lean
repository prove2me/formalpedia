-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_exists_smul_idem
-- name    : GlobalTheory.DRFil.exists_smul_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:45.236246+00:00
-- url     : https://prove2.me/theorems/577e327f-d453-432f-9c86-db18f80243eb
-- title:
--   DRFil: exists smul idem
-- statement:
--   The DRFil construction uses the exists smul idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L248-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean#L248-L254

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

theorem GlobalTheory.DRFil.exists_smul_idem (τ : K →ₐ[Qp] LL) (n : ℕ) (a : Fin n → LL) (c : Fin n → K) :
    idem F τ * ∑ i, a i ⊗ₜ[Qp] algebraMap K F (c i) = (∑ i, a i * τ (c i)) • idem F τ := by sorry
