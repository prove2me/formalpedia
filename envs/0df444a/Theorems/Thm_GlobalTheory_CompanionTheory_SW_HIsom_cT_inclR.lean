-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_cT_inclR
-- name    : GlobalTheory.CompanionTheory.SW.HIsom.cT_inclR
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:46.331218+00:00
-- url     : https://prove2.me/theorems/40564fa7-96db-43df-ad8f-90e610ee8823
-- title:
--   HIsom: c T incl R
-- statement:
--   The HIsom construction uses the c T incl R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean#L70-L73

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HIsom
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.HIsom.cT_inclR (σ : E →ₐ[F] E) {M : ℕ} (g : Matrix (Fin M) (Fin M) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by sorry
