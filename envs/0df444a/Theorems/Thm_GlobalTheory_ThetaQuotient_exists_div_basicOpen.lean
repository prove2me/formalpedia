-- Prove2me | Theorems.Thm_GlobalTheory_ThetaQuotient_exists_div_basicOpen
-- name    : GlobalTheory.ThetaQuotient.exists_div_basicOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:09.803456+00:00
-- url     : https://prove2.me/theorems/85a2d086-baa8-476c-8ebd-20d88ea42d1d
-- title:
--   Theta Quotient: exists div basic Open
-- statement:
--   The Theta Quotient construction uses the exists div basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EvalDivOfIsHomogeneous.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EvalDivOfIsHomogeneous.lean#L60-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EvalDivOfIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaQuotient

theorem GlobalTheory.ThetaQuotient.exists_div_basicOpen {X : Scheme.{0}} {U : X.Opens} (f g : Γ(X, U)) :
    ∃ s : Γ(X, X.basicOpen g), ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ X.basicOpen g →
      valAt' x (X.basicOpen g) s = valAt' x U f / valAt' x U g := by sorry
