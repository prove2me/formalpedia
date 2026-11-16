-- Prove2me | Theorems.Thm_Kyprianou_Ch02_chapterTwoMainResultsV3
-- name    : Kyprianou.Ch02.chapterTwoMainResultsV3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:30:40.559866+00:00
-- url     : https://prove2.me/theorems/9efa20da-815c-4b3a-a17b-a124aefc83a5
-- title:
--   Chapter 2 V3: all numbered results and Exercises 2.1-2.12
-- statement:
--   The conjunction of all mandatory Chapter 2 numbered results, including the general Poisson measure constructions and both clauses of compensated Poisson martingales, the corrected subordinator criterion, all twelve complete exercises with their individual parts, and the retained useful published Lévy-Itô supporting milestones. Each conjunct reproduces the complete proposition of one independently linked mandatory milestone.
-- source:
--   A. E. Kyprianou (2006), Chapter 2, pp. 33-66 and original exercise solutions pp. 307-311; mathematical source errata recorded

import Mathlib
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV2
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV3
open MeasureTheory ProbabilityTheory Kyprianou
set_option autoImplicit false

theorem Kyprianou.Ch02.chapterTwoMainResultsV3 :
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureExists ∧
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureSupportCountable ∧
    Kyprianou.Ch02.certificateV2_poissonRandomMeasureIntegralLaws ∧
    Kyprianou.Ch02.certificateV2_largeJumpProcessLevy ∧
    Kyprianou.Ch02.certificateV2_sumOfIndependentLevyProcesses ∧
    Kyprianou.Ch02.certificateV2_compensatedBandIsL2Martingale ∧
    Kyprianou.Ch02.certificateV2_smallJumpLimitCadlag ∧
    Kyprianou.Ch02.certificateV2_levyItoDecomposition ∧
    Kyprianou.Ch02.certificateV2_boundedVariationCriterionCh02 ∧
    Kyprianou.Ch02.certificateV3_compoundPoissonDriftPathCriterionCh02V3 ∧
    Kyprianou.Ch02.certificateV3_independentSubordinationCh02V3 ∧
    Kyprianou.Ch02.certificateV3_subordinatorCriterionCh02V3 ∧
    Kyprianou.Ch02.certificateV3_markedCompoundPoissonRandomMeasureCh02V4 ∧
    Kyprianou.Ch02.certificateV3_poissonRandomMeasureExistsGenericCh02V3 ∧
    Kyprianou.Ch02.certificateV3_poissonRestrictionAndIndependenceCh02V3 ∧
    Kyprianou.Ch02.certificateV3_finiteRegionPoissonIntegralCh02V3 ∧
    Kyprianou.Ch02.certificateV3_compensatedGeneralRegionMartingaleCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_1_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_3_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_4_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_6_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_8_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_11_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_2_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_7_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_10_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_5_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_9_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_12_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_poissonRandomMeasureSupportGenericCh02V3 := by sorry
