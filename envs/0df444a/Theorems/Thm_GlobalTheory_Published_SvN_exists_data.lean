-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_exists_data
-- name    : GlobalTheory.Published.SvN.exists_data
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:15.850956+00:00
-- url     : https://prove2.me/theorems/d1306471-2c82-40d7-b64d-dd96120ec352
-- title:
--   Sv N: exists data
-- statement:
--   The Sv N construction uses the exists data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L426-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L426-L512

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
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {W : Type} [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}
variable [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]

theorem GlobalTheory.Published.SvN.exists_data (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) (hn : B.Nondegenerate) {ψ : AddChar F ℂ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ (A : AddSubgroup W) (α : W → ℂ), Splits (fun x y => ψ (B x y / 2)) A α ∧ (alt_psi hB ψ).perp A ≤ A ∧
      (∀ᶠ u in 𝓝 (0 : W), u ∈ A ∧ α u = 1) ∧
      (∀ N ∈ 𝓝 (0 : W), ∃ T, ((alt_psi hB ψ).perp T : Set W) ⊆ N ∧ Finite (A ⧸ ((alt_psi hB ψ).perp T).addSubgroupOf A)) ∧
      ∀ w, ∀ᶠ u in 𝓝 (0 : W), ψ (B u w / 2) ^ 2 = 1 := by sorry
