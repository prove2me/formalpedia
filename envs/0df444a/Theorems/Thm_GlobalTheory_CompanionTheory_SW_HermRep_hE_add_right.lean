-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_hE_add_right
-- name    : GlobalTheory.CompanionTheory.SW.HermRep.hE_add_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:28.18681+00:00
-- url     : https://prove2.me/theorems/089c8708-feeb-45d3-80ac-6c84b7bbcfc8
-- title:
--   Herm Rep: h E add right
-- statement:
--   The Herm Rep construction uses the h E add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianNondegRepresentsNonzeroScalar.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianNondegRepresentsNonzeroScalar.lean#L34-L36

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (T : Matrix (Fin M) (Fin M) E)

theorem GlobalTheory.CompanionTheory.SW.HermRep.hE_add_right (x y y' : Fin M → E) :
    hE σ T x (y + y') = hE σ T x y + hE σ T x y' := by sorry
