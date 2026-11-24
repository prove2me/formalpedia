-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_coords_ratTup
-- name    : GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:39.50646+00:00
-- url     : https://prove2.me/theorems/7d7b5ebe-3520-494b-b755-5bf194495c8f
-- title:
--   Rat Coord: coords rat Tup
-- statement:
--   The Rat Coord construction uses the coords rat Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteComponentCoordinatesAction.lean#L49-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteComponentCoordinatesAction.lean#L49-L86

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteComponentCoordinatesAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord

theorem GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (ω : HA (AF F) σ J) (x : Fin M × Fin d → F), (∀ w, xw e b (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x)))) w = ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ∧ cv (Af F) b (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x))) 0) = gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j) := by sorry
