-- Prove2me | Theorems.Thm_GlobalTheory_WeilExp_cancel_frames
-- name    : GlobalTheory.WeilExp.cancel_frames
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:22.188652+00:00
-- url     : https://prove2.me/theorems/6dfb06fd-af6f-44a7-80dd-f226faa9b6fa
-- title:
--   Weil Exp: cancel frames
-- statement:
--   The Weil Exp construction uses the cancel frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/WeilIsExpRiemannForm.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/WeilIsExpRiemannForm.lean#L69-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_WeilIsExpRiemannForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.WeilExp

theorem GlobalTheory.WeilExp.cancel_frames {A₁ A₂ B₁ B₂ F₀ Fa Fb Fab Ca Cb e₁ e₂ e₃ e₄ c : ℂ} (ha : Fa ≠ 0) (hb : Fb ≠ 0)
    (hab : Fab ≠ 0) (h₁ : A₁ * Fa = Ca * e₁ * F₀) (h₂ : A₂ * Fab = Cb * e₂ * Fa)
    (h₃ : B₁ * Fb = Cb * e₃ * F₀) (h₄ : B₂ * Fab = Ca * e₄ * Fb) (he : e₁ * e₂ = e₃ * e₄ * c) :
    A₁ * A₂ = B₁ * B₂ * c := by sorry
