-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_isHolFam_vtfQ
-- name    : GlobalTheory.AnVal.isHolFam_vtfQ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:19.134589+00:00
-- url     : https://prove2.me/theorems/cd3aea6b-55aa-5401-a3fb-fd34d6701abe
-- title:
--   An Val: is Hol Fam vtf Q
-- statement:
--   The An Val construction uses the is Hol Fam vtf Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/SectionReadingExistsUniqueIsTheta.lean#L18-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/SectionReadingExistsUniqueIsTheta.lean#L18-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SectionReadingExistsUniqueIsTheta
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem GlobalTheory.AnVal.isHolFam_vtfQ {x0 : Sp ℂ ⟶ S} {g : ℕ} (e : (Fin g → ℂ) → (Over.mk x0 ⟶ A))
    (hol : IsHolFam (fun z => (e z).left)) : IsHolFam (fun z => (vtfQ A (e z)).left) := by sorry
