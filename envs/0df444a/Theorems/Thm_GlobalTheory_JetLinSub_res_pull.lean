-- Prove2me | Theorems.Thm_GlobalTheory_JetLinSub_res_pull
-- name    : GlobalTheory.JetLinSub.res_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T18:41:16.775227+00:00
-- url     : https://prove2.me/theorems/daaf3307-af2a-567d-a27e-5d1ad6e6b101
-- title:
--   Jet Lin Sub: res pull
-- statement:
--   The Jet Lin Sub construction uses the res pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean#L146-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean#L146-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub

theorem GlobalTheory.JetLinSub.res_pull {Y Z : Scheme.{0}} (s : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : ⊤ ≤ W) (h' : ⊤ ≤ W')
    (le : W' ≤ s ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (Z.presheaf.map (homOfLE h').op).hom ((Z.presheaf.map (homOfLE le).op).hom ((s.app W).hom x)) =
      s.appTop.hom ((Y.presheaf.map (homOfLE h).op).hom x) := by sorry
