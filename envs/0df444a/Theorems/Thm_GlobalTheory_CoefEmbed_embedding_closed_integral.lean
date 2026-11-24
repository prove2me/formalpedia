-- Prove2me | Theorems.Thm_GlobalTheory_CoefEmbed_embedding_closed_integral
-- name    : GlobalTheory.CoefEmbed.embedding_closed_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:42.76893+00:00
-- url     : https://prove2.me/theorems/0a123ebe-14d8-4855-8e24-7dc0a04a5e0e
-- title:
--   Coef Embed: embedding closed integral
-- statement:
--   The Coef Embed construction uses the embedding closed integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EmbeddingClosedIntegral.lean#L92-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EmbeddingClosedIntegral.lean#L92-L277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EmbeddingClosedIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoefEmbed
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem GlobalTheory.CoefEmbed.embedding_closed_integral : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ κ : FractionRing O →+* PadicAlgCl l, (∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → Topology.IsEmbedding (fun x : O => κ (algebraMap O (FractionRing O) x)) ∧ IsClosed (Set.range κ) ∧ (∀ x : FractionRing O, ‖κ x‖ ≤ 1 → ∃ y : O, algebraMap O (FractionRing O) y = x) ∧ ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by sorry
