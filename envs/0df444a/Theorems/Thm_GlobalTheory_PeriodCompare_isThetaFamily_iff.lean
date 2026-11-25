-- Prove2me | Theorems.Thm_GlobalTheory_PeriodCompare_isThetaFamily_iff
-- name    : GlobalTheory.PeriodCompare.isThetaFamily_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:27.590852+00:00
-- url     : https://prove2.me/theorems/8c7eaf72-dd16-5abf-b39c-18cf9fcd065b
-- title:
--   Period Compare: is Theta Family iff
-- statement:
--   The Period Compare construction uses the is Theta Family iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L301-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L301-L326

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {g m : ℕ}

theorem GlobalTheory.PeriodCompare.isThetaFamily_iff (L : RigLB G) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ S))
    (ex : ∀ b : Fin m → ℂ, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) :
    IsThetaFamily L B y ex θ ↔
      HolOn (B ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun p => ((ex p.1 p.2).left : Sp ℂ ⟶ G.left)) ∧
      (∀ b ∈ B, (ex b 0).left = y b ≫ eSec G) ∧ Tor.IsThetaFrame L B y (fun b z => (ex b z).left) θ := by sorry
