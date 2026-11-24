-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_real_iso
-- name    : GlobalTheory.CompanionTheory.SW.real_iso
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:12:23.255411+00:00
-- url     : https://prove2.me/theorems/b88c14d6-8823-4374-9ff6-c8f99e8112f9
-- title:
--   SW: real iso
-- statement:
--   The SW construction uses the real iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean#L170-L173

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
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
open GlobalTheory.CompanionTheory.SW.RealCoord

theorem GlobalTheory.CompanionTheory.SW.real_iso : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∃ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) ∧ IsHomeomorph e ∧ (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) ∧ (∀ y w, |e y w| = ‖y w‖) ∧ ∀ lam : Measure (Ainf F), IsStdInf lam → lam.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by sorry
