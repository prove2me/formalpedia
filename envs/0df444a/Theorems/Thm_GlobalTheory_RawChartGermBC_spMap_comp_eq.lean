-- Prove2me | Theorems.Thm_GlobalTheory_RawChartGermBC_spMap_comp_eq
-- name    : GlobalTheory.RawChartGermBC.spMap_comp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:32.722188+00:00
-- url     : https://prove2.me/theorems/4a31a62c-d9cf-46fc-a81c-7ce24394bb46
-- title:
--   Raw Chart Germ BC: sp Map comp eq
-- statement:
--   The Raw Chart Germ BC construction uses the sp Map comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RawChartBaseChangeRigGerm.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RawChartBaseChangeRigGerm.lean#L37-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RawChartBaseChangeRigGerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RawChartGermBC
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem GlobalTheory.RawChartGermBC.spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* D) (f' : A →+* C) (g' : C →+* D) (h : g.comp f = g'.comp f') :
    (spMap g ≫ spMap f : Sp D ⟶ Sp A) = spMap g' ≫ spMap f' := by sorry
