-- Prove2me | Theorems.Thm_GlobalTheory_RawChartGermBC_isPullSec_whisker_comp
-- name    : GlobalTheory.RawChartGermBC.isPullSec_whisker_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:15:27.777504+00:00
-- url     : https://prove2.me/theorems/09284170-07df-4732-aa0a-9f2c1323d034
-- title:
--   Raw Chart Germ BC: is Pull Sec whisker comp
-- statement:
--   The Raw Chart Germ BC construction uses the is Pull Sec whisker comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RawChartBaseChangeRigGerm.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RawChartBaseChangeRigGerm.lean#L55-L61

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
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
set_option maxHeartbeats 1000000

theorem GlobalTheory.RawChartGermBC.isPullSec_whisker_comp (a : ℤ) {T1 T2 T3 : Over S0} (h1 : T2 ⟶ T1) (h2 : T3 ⟶ T2)
    {s1 : LB.Sec (LPow A L a T1)} {s2 : LB.Sec (LPow A L a T2)} {s3 : LB.Sec (LPow A L a T3)}
    (e1 : IsPullSec A L a (h1 ▷ A) (whiskerRight_snd _ _) s1 s2)
    (e2 : IsPullSec A L a (h2 ▷ A) (whiskerRight_snd _ _) s2 s3) :
    IsPullSec A L a ((h2 ≫ h1) ▷ A) (whiskerRight_snd _ _) s1 s3 := by sorry
