-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_sigR_inclR
-- name    : GlobalTheory.CompanionTheory.SW.HermTop.sigR_inclR
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:24.151812+00:00
-- url     : https://prove2.me/theorems/1bbbeae1-7c27-4a8c-abc0-84f8264753fe
-- title:
--   Herm Top: sig R incl R
-- statement:
--   The Herm Top construction uses the sig R incl R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorel.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorel.lean#L26-L27

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.HermTop.sigR_inclR (σ : E →ₐ[F] E) (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by sorry
