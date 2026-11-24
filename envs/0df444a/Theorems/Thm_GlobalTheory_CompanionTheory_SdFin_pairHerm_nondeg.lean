-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_pairHerm_nondeg
-- name    : GlobalTheory.CompanionTheory.SdFin.pairHerm_nondeg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:00:34.624854+00:00
-- url     : https://prove2.me/theorems/e0e53c40-fe22-407a-ad9d-8eadef935d40
-- title:
--   Sd Fin: pair Herm nondeg
-- statement:
--   The Sd Fin construction uses the pair Herm nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean#L293-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean#L293-L315

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SdFin
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem GlobalTheory.CompanionTheory.SdFin.pairHerm_nondeg [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero F]
    (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (S : HermR R σ n) (h : ∀ T, pairHerm R σ n S T = 0) : S = 0 := by sorry
