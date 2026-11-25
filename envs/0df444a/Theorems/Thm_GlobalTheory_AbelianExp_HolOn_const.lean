-- Prove2me | Theorems.Thm_GlobalTheory_AbelianExp_HolOn_const
-- name    : GlobalTheory.AbelianExp.HolOn.const
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:18.822011+00:00
-- url     : https://prove2.me/theorems/1a719bd6-8bf2-49f7-a241-96f097877be4
-- title:
--   Hol On: const
-- statement:
--   The Hol On construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ContinuousOnValue.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ContinuousOnValue.lean#L40-L46

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

theorem GlobalTheory.AbelianExp.HolOn.const (hW : IsOpen W) (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) : HolOn W fun _ => x := by sorry
