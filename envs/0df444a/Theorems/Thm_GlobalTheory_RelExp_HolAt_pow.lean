-- Prove2me | Theorems.Thm_GlobalTheory_RelExp_HolAt_pow
-- name    : GlobalTheory.RelExp.HolAt.pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:41.116462+00:00
-- url     : https://prove2.me/theorems/bbda1718-78e4-4ab4-badc-bf690a3081f8
-- title:
--   Hol At: pow
-- statement:
--   The Hol At construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EventuallyEqOfAdditiveOfHasFDerivAt.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EventuallyEqOfAdditiveOfHasFDerivAt.lean#L170-L174

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
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : E → (Sp ℂ ⟶ X)} {w₀ : E}

theorem GlobalTheory.RelExp.HolAt.pow {a : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀) (n : ℕ) :
    HolAt (Z := G.left) (fun w => (a w ^ n).left) w₀ := by sorry
