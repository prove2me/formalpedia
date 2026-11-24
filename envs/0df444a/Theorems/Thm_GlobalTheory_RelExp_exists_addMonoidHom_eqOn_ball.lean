-- Prove2me | Theorems.Thm_GlobalTheory_RelExp_exists_addMonoidHom_eqOn_ball
-- name    : GlobalTheory.RelExp.exists_addMonoidHom_eqOn_ball
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:13.934644+00:00
-- url     : https://prove2.me/theorems/baa4c78b-ce73-4810-b8b3-48a6c1c19c87
-- title:
--   Rel Exp: exists add Monoid Hom eq On ball
-- statement:
--   The Rel Exp construction uses the exists add Monoid Hom eq On ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EventuallyEqOfAdditiveOfHasFDerivAt.lean#L182-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EventuallyEqOfAdditiveOfHasFDerivAt.lean#L182-L207

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.RelExp
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {Z Y : Scheme.{0}}
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]

theorem GlobalTheory.RelExp.exists_addMonoidHom_eqOn_ball {g : V → A} {r : ℝ} (hr : 0 < r)
    (hg : ∀ x ∈ Metric.ball (0 : V) r, ∀ x' ∈ Metric.ball (0 : V) r, g (x + x') = g x + g x') :
    ∃ e : V →+ A, ∀ x ∈ Metric.ball (0 : V) r, e x = g x := by sorry
