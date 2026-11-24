-- Prove2me | Theorems.Thm_GlobalTheory_RawChartBC_isCombAt_map
-- name    : GlobalTheory.RawChartBC.isCombAt_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:15:05.77836+00:00
-- url     : https://prove2.me/theorems/0d50c081-da18-4cdd-88ba-0d812eb19d5c
-- title:
--   Raw Chart BC: is Comb At map
-- statement:
--   The Raw Chart BC construction uses the is Comb At map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsRawChartBaseChangeJetPoints.lean#L153-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsRawChartBaseChangeJetPoints.lean#L153-L164

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawChartBC
open ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)

theorem GlobalTheory.RawChartBC.isCombAt_map {k : ℕ} {v : Fin k → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin k → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x0 v cf w) :
    IsCombAt (spMap ψ ≫ x0) (fun i => spMap (dualMap ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMap ψ) ≫ w) := by sorry
