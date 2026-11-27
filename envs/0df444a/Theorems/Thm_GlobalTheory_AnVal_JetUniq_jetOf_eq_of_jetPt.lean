-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_JetUniq_jetOf_eq_of_jetPt
-- name    : GlobalTheory.AnVal.JetUniq.jetOf_eq_of_jetPt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:14.083894+00:00
-- url     : https://prove2.me/theorems/3b06b046-7d91-5a40-80c5-9ec563ba54a2
-- title:
--   Jet Uniq: jet Of eq of jet Pt
-- statement:
--   The Jet Uniq construction uses the jet Of eq of jet Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FderivEqOfJetOf.lean#L176-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FderivEqOfJetOf.lean#L176-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
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
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetUniq
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.AnVal.JetUniq.jetOf_eq_of_jetPt {g : ℕ} {Y : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (hol' : IsHolFam e') (m : ℕ) (h : PullbackSections.jetPt e hol m = PullbackSections.jetPt e' hol' m) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (hU' : e' 0 cpt ∈ U) (f : Γ(Y, U)) :
    PullbackSections.jetOf m (fun z => valAt' (e z) U f) = PullbackSections.jetOf m (fun z => valAt' (e' z) U f) := by sorry
