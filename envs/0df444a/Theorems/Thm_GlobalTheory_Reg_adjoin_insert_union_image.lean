-- Prove2me | Theorems.Thm_GlobalTheory_Reg_adjoin_insert_union_image
-- name    : GlobalTheory.Reg.adjoin_insert_union_image
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:20:47.726208+00:00
-- url     : https://prove2.me/theorems/6edc376c-877d-4cdb-a6e6-18f78cb1e34e
-- title:
--   Reg: adjoin insert union image
-- statement:
--   The Reg construction uses the adjoin insert union image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsRefinedCoveringChartFamily.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsRefinedCoveringChartFamily.lean#L17-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AdjoinRatiosOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_NaturalRuleValueBaseChangeOfIsReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SpanEvalEqTopOfNoCommonZeroReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsRefinedCoveringChartFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory GlobalTheory.Reg

theorem GlobalTheory.Reg.adjoin_insert_union_image {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [DecidableEq Ω] (x : Ω)
    (G : Finset Ω) {m : ℕ} (r : Fin m → Ω) :
    Algebra.adjoin K (insert x ((G ∪ Finset.univ.image r : Finset Ω) : Set Ω)) =
      Algebra.adjoin K ((Algebra.adjoin K (insert x (G : Set Ω)) : Set Ω) ∪ Set.range r) := by sorry
