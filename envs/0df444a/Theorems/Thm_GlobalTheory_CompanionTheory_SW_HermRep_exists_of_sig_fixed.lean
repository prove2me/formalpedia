-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_exists_of_sig_fixed
-- name    : GlobalTheory.CompanionTheory.SW.HermRep.exists_of_sig_fixed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:07:13.636136+00:00
-- url     : https://prove2.me/theorems/65f3241c-f144-4048-82c7-1a3e9fa40724
-- title:
--   Herm Rep: exists of sig fixed
-- statement:
--   The Herm Rep construction uses the exists of sig fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianNondegRepresentsNonzeroScalar.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianNondegRepresentsNonzeroScalar.lean#L19-L21

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem GlobalTheory.CompanionTheory.SW.HermRep.exists_of_sig_fixed (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ t : F, algebraMap F E t = x := by sorry
