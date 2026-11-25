-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_embedding
-- name    : GlobalTheory.LocMod.Inhab.exists_embedding
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:04.655508+00:00
-- url     : https://prove2.me/theorems/d8dac5f4-c0ba-43df-b101-12c9ac6bb46d
-- title:
--   Inhab: exists embedding
-- statement:
--   The Inhab construction uses the exists embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L167-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L167-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem GlobalTheory.LocMod.Inhab.exists_embedding {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (ρ σ : Matrix Y Y' k → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f)
    (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f)
    (hc : ∀ x y f, ρ x (σ y f) = pairing ψ x y • σ y (ρ x f)) (P : Submodule ℂ V)
    (hP : ∀ x, ∀ f ∈ P, ρ x f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P) {g : V} (hg : g ∈ P) (g0 : g ≠ 0)
    (hg1 : ∀ x ∈ box Y Y' (1 : kˣ), ρ x g = g)
    (hg2 : ∀ y, (∀ x ∈ box Y Y' (1 : kˣ), pairing ψ x y = 1) → σ y g = g) :
    ∃ T : (Matrix Y Y' k → ℂ) →ₗ[ℂ] V, ∀ Φ ∈ SB (Matrix Y Y' k), (T Φ = 0 → Φ = 0) ∧ T Φ ∈ P ∧
      (∀ x, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ ∀ y, T (fun t => pairing ψ t y * Φ t) = σ y (T Φ) := by sorry
