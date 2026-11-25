-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_plane_model
-- name    : GlobalTheory.Published.SvN.plane_model
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:06.159553+00:00
-- url     : https://prove2.me/theorems/2adcd150-7230-4277-9238-0411a1c8abb6
-- title:
--   Sv N: plane model
-- statement:
--   The Sv N construction uses the plane model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L727-L733
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L727-L733

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

theorem GlobalTheory.Published.SvN.plane_model (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (h2 : (2 : F) ≠ 0) :
    (∃ g k : Heisenberg (planeForm F), g * k ≠ k * g) ∧
    ∃ ψ : AddChar F ℂ, Continuous ψ ∧ ψ ≠ 1 ∧ ∃ (S : Type) (_ : AddCommGroup S) (_ : Module ℂ S)
      (ρ : Representation ℂ (Heisenberg (planeForm F)) S), Heisenberg.IsIrrSmoothOf ψ ρ := by sorry
