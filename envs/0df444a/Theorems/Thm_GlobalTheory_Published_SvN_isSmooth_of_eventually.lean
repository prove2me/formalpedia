-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_isSmooth_of_eventually
-- name    : GlobalTheory.Published.SvN.isSmooth_of_eventually
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:25.780523+00:00
-- url     : https://prove2.me/theorems/6a041f65-976a-48bd-a6db-efd8f932fc6f
-- title:
--   Sv N: is Smooth of eventually
-- statement:
--   The Sv N construction uses the is Smooth of eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L560-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L560-L579

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

theorem GlobalTheory.Published.SvN.isSmooth_of_eventually (hψ : Continuous ψ) (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v)
    (hs : ∀ v, ∀ᶠ u in 𝓝 (0 : W), π ⟨u, 0⟩ v = v) : PRep.IsSmooth π := by sorry
