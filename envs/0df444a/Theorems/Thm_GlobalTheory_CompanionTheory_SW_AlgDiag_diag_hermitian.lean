-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AlgDiag_diag_hermitian
-- name    : GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:30:31.420033+00:00
-- url     : https://prove2.me/theorems/2f84c8b3-555d-5832-bf9a-c70699e0db6c
-- title:
--   Alg Diag: diag hermitian
-- statement:
--   The Alg Diag construction uses the diag hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormDiagonalizesOverField.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormDiagonalizesOverField.lean#L31-L32

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SplitAnisotropic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DiagHermitian
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormDiagonalizesOverField
import Theorems.Thm_UpperTheory_Reformulated_B_Gka4_diag_hermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AlgDiag

theorem GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), IsHermND σ T → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g = Matrix.diagonal fun i => algebraMap F E (D i : F) := by sorry
