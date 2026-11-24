-- Prove2me | Theorems.Thm_GlobalTheory_RelExp_eventuallyEq_of_additive_of_hasFDerivAt
-- name    : GlobalTheory.RelExp.eventuallyEq_of_additive_of_hasFDerivAt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:20:57.484883+00:00
-- url     : https://prove2.me/theorems/13599802-4f65-46c1-a2df-0e160be54a0b
-- title:
--   Rel Exp: eventually Eq of additive of has FDeriv At
-- statement:
--   The Rel Exp construction uses the eventually Eq of additive of has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EventuallyEqOfAdditiveOfHasFDerivAt.lean#L211-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EventuallyEqOfAdditiveOfHasFDerivAt.lean#L211-L220

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

theorem GlobalTheory.RelExp.eventuallyEq_of_additive_of_hasFDerivAt {ζ : E → E'} {T : E →L[ℂ] E'} (hT : HasFDerivAt ζ T 0)
    (hζ : ∀ᶠ p in 𝓝 (0 : E × E), ζ (p.1 + p.2) = ζ p.1 + ζ p.2) : ζ =ᶠ[𝓝 0] T := by sorry
