-- Prove2me | Theorems.Thm_GlobalTheory_AdmissibleProjection_exists_irreducible_equivariant_projection
-- name    : GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:27.080243+00:00
-- url     : https://prove2.me/theorems/f2e066a4-b4a3-4f6b-99d7-a5ddecc72489
-- title:
--   Admissible Projection: exists irreducible equivariant projection
-- statement:
--   The Admissible Projection construction uses the exists irreducible equivariant projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducibleEquivariantProjection.lean#L91-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducibleEquivariantProjection.lean#L91-L179

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducibleEquivariantProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdmissibleProjection
open GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection : ∀ (H W : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H)) → (∀ w, IsOpen {k : H | ρ k w = w}) → (∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) → ∀ x : W, x ≠ 0 → ∃ (U : Submodule ℂ W) (P : W →ₗ[ℂ] W), U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) ∧ (∀ w, P w ∈ U) ∧ (∀ g w, P (ρ g w) = ρ g (P w)) ∧ P x ≠ 0 := by sorry
