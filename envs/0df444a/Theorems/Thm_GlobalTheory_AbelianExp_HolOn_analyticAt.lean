-- Prove2me | Theorems.Thm_GlobalTheory_AbelianExp_HolOn_analyticAt
-- name    : GlobalTheory.AbelianExp.HolOn.analyticAt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:33.790873+00:00
-- url     : https://prove2.me/theorems/1e13f873-6f5f-458b-87c3-f6999fc4e846
-- title:
--   Hol On: analytic At
-- statement:
--   The Hol On construction uses the analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ContinuousOnValue.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ContinuousOnValue.lean#L109-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ContinuousOnValue
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
open GlobalTheory GlobalTheory.AbelianExp
attribute [local instance] pointTopology
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {W : Set E} {X Y : Over (Sp ℂ)} {a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)}

theorem GlobalTheory.AbelianExp.HolOn.analyticAt [FiniteDimensional ℂ E] (h : HolOn W a) {g : ℕ} {U : X.left.Opens}
    (t : Fin g → Γ(X.left, U)) {w : E} (hw : w ∈ W) (hU : ⊤ ≤ (a w).left ⁻¹ᵁ U) :
    AnalyticAt ℂ (fun w i => valAt' (a w).left U (t i)) w := by sorry
