-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_exists_eigen_mem
-- name    : GlobalTheory.Published.SvN.exists_eigen_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:48.931802+00:00
-- url     : https://prove2.me/theorems/5f34f2c0-324b-4029-9b04-03561661f360
-- title:
--   Sv N: exists eigen mem
-- statement:
--   The Sv N construction uses the exists eigen mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L588-L594
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L588-L594

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open Heisenberg
variable {F W M : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W} [AddCommGroup M] [Module ℂ M]
  {ψ : AddChar F ℂ} {π : Representation ℂ (Heisenberg B) M}
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [TopologicalSpace W]
  [IsModuleTopology F W]
variable (hB : B.IsAlt) {A : AddSubgroup W} {α : W → ℂ} (hα : Splits (fun x y => ψ (B x y / 2)) A α)
  (hA : (alt_psi hB ψ).perp A ≤ A) (h1 : ∀ᶠ u in 𝓝 (0 : W), u ∈ A ∧ α u = 1)
  (h2 : ∀ N ∈ 𝓝 (0 : W), ∃ T, ((alt_psi hB ψ).perp T : Set W) ⊆ N ∧ Finite (A ⧸ ((alt_psi hB ψ).perp T).addSubgroupOf A))
  (h3 : ∀ w, ∀ᶠ u in 𝓝 (0 : W), ψ (B u w / 2) ^ 2 = 1)
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [IsModuleTopology F W]
include hα h1 h2

theorem GlobalTheory.Published.SvN.exists_eigen_mem (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) (hs : PRep.IsSmooth π) (P : Subrepresentation π) (hP : P ≠ ⊥) :
    ∃ e ∈ P.toSubmodule, e ≠ 0 ∧ ∀ a ∈ A, π ⟨a, 0⟩ e = α a • e := by sorry
