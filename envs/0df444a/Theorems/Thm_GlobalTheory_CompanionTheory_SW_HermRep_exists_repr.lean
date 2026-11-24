-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_exists_repr
-- name    : GlobalTheory.CompanionTheory.SW.HermRep.exists_repr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:33.889885+00:00
-- url     : https://prove2.me/theorems/5945ccfb-6cb4-4df2-a96d-9381e03fd580
-- title:
--   Herm Rep: exists repr
-- statement:
--   The Herm Rep construction uses the exists repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianNondegRepresentsNonzeroScalar.lean#L50-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianNondegRepresentsNonzeroScalar.lean#L50-L75

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_EqIdOfFixed
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermRep

theorem GlobalTheory.CompanionTheory.SW.HermRep.exists_repr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ T → ∃ (t : F) (x : Fin (n + 1) → E), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by sorry
