-- Prove2me | Theorems.Thm_GlobalTheory_LB_chartEquiv_pullSec
-- name    : GlobalTheory.LB.chartEquiv_pullSec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:42.788337+00:00
-- url     : https://prove2.me/theorems/4aca4c1b-7958-46cb-847b-378ca675648c
-- title:
--   LB: chart Equiv pull Sec
-- statement:
--   The LB construction uses the chart Equiv pull Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/BijectiveSmulChartSec.lean#L733-L738
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/BijectiveSmulChartSec.lean#L733-L738

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
variable (L : LB X)
variable {L}
variable (f : Y ⟶ X)

theorem GlobalTheory.LB.chartEquiv_pullSec (hL : L.IsLB) (j : (L.pull f).ι) {V : X.Opens}
    (h : V ≤ L.U (j PUnit.unit)) (h' : f ⁻¹ᵁ V ≤ (L.pull f).U j) (s : Γ(toMod L, V)) :
    chartEquiv (Semi.LB.isLB_pull hL f) j h' (pullSec L f V s) =
      (f.app V).hom (chartEquiv hL (j PUnit.unit) h s) := by sorry
