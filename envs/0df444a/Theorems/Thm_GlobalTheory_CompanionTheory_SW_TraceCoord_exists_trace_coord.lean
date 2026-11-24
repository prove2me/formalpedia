-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_exists_trace_coord
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:11:26.193968+00:00
-- url     : https://prove2.me/theorems/fda18487-4b2f-4dc5-9543-76e8c9e317b1
-- title:
--   Trace Coord: exists trace coord
-- statement:
--   The Trace Coord construction uses the exists trace coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L188-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L188-L220

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) ∧ ∀ h : HA R σ J, ∀ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, (∀ p q, g p q = (Algebra.TensorProduct.basis R b).repr ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2) → gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ x : Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := by sorry
