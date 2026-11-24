-- Prove2me | Theorems.Thm_GlobalTheory_MulPullSec_exists_pull_sec
-- name    : GlobalTheory.MulPullSec.exists_pull_sec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:44.342803+00:00
-- url     : https://prove2.me/theorems/0f244771-e4fc-4ce4-a8a5-03bd82dac09c
-- title:
--   Mul Pull Sec: exists pull sec
-- statement:
--   The Mul Pull Sec construction uses the exists pull sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulPullSec.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulPullSec.lean#L45-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulPullSec
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem GlobalTheory.MulPullSec.exists_pull_sec (hL : L.IsLB) (f : X ⟶ X) (m : ℤ) (N M : ℕ) (hM : (M : ℤ) = m * N)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![m, -1])) (hα : α.IsGen) (h : (lbPow L N).Sec) :
    ∃ h' : (lbPow L M).Sec, Out.nonzeroLocus h' = f ⁻¹ᵁ Out.nonzeroLocus h := by sorry
