-- Prove2me | Theorems.Thm_GlobalTheory_T_coordinate_bijection_trace_form
-- name    : GlobalTheory.T.coordinate_bijection_trace_form
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:59.636291+00:00
-- url     : https://prove2.me/theorems/c5c77cc3-6d64-4252-9ece-3dedac17fa5b
-- title:
--   T: coordinate bijection trace form
-- statement:
--   The T construction uses the coordinate bijection trace form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateBijectionTraceFormStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateBijectionTraceFormStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coordinate_bijection_trace_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧ (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧ ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (β : F) (x : Fin M × Fin d → F), gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by sorry
