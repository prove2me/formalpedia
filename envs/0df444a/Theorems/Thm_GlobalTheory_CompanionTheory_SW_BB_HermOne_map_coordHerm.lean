-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_HermOne_map_coordHerm
-- name    : GlobalTheory.CompanionTheory.SW.BB.HermOne.map_coordHerm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:45.232883+00:00
-- url     : https://prove2.me/theorems/047181c1-d1b5-4b73-b514-e6537de06203
-- title:
--   Herm One: map coord Herm
-- statement:
--   The Herm One construction uses the map coord Herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianRankOneHomeomorphBase.lean#L178-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianRankOneHomeomorphBase.lean#L178-L234

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianRankOneHomeomorphBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.HermOne
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R] [IsTopologicalRing R]
variable [MeasurableSpace R] [BorelSpace R]

theorem GlobalTheory.CompanionTheory.SW.BB.HermOne.map_coordHerm (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    [SigmaFinite lam] : (coordHerm R σ b lam 1).map (hermHomeo R hcm) = lam := by sorry
