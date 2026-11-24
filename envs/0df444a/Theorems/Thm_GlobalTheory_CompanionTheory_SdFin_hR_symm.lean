-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_hR_symm
-- name    : GlobalTheory.CompanionTheory.SdFin.hR_symm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:00:13.264213+00:00
-- url     : https://prove2.me/theorems/7309903a-cd02-41c3-a682-5eb7d49fff32
-- title:
--   Sd Fin: h R symm
-- statement:
--   The Sd Fin construction uses the h R symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean#L224-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean#L224-L235

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

theorem GlobalTheory.CompanionTheory.SdFin.hR_symm [FiniteDimensional F E] (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    (x y : Fin M → R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = Algebra.trace R (R ⊗[F] E) (hR R σ J y x) := by sorry
