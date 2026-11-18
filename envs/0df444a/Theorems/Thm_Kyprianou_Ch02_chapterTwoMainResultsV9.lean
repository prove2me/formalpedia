-- Prove2me | Theorems.Thm_Kyprianou_Ch02_chapterTwoMainResultsV9
-- name    : Kyprianou.Ch02.chapterTwoMainResultsV9
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T12:51:49.204317+00:00
-- url     : https://prove2.me/theorems/944d2e0a-2461-474b-990e-50aab9266abc
-- title:
--   Chapter 2 V9: thirty source-fidelitous cumulative milestone certificates
-- statement:
--   Complete cumulative conjunction of thirty Chapter 2 results and whole exercises, with source-general Poisson existence and restriction under the counting-measure Definition 2.3 contract.
-- source:
--   Kyprianou (2006), Chapter 2, printed pp. 33–66; source corrections recorded 17 November 2026

import Mathlib
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV2
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV9
open MeasureTheory ProbabilityTheory Kyprianou
set_option autoImplicit false

theorem Kyprianou.Ch02.chapterTwoMainResultsV9 :
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
    Kyprianou.Ch02.certificateV6_markedCompoundPoissonRandomMeasureCh02V6 ∧
    Kyprianou.Ch02.certificateV9_poissonRandomMeasureExistsGenericCh02V9 ∧
    Kyprianou.Ch02.certificateV9_poissonRestrictionAndIndependenceGenericCh02V9 ∧
    Kyprianou.Ch02.certificateV3_finiteRegionPoissonIntegralCh02V3 ∧
    Kyprianou.Ch02.certificateV3_compensatedGeneralRegionMartingaleCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_1_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_3_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_4_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_6_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_8_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_11_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV6_exercise2_2_AllPartsCh02V6 ∧
    Kyprianou.Ch02.certificateV3_exercise2_7_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_10_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_5_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV4_exercise2_9_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV4_exercise2_12_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV5_poissonRandomMeasureSupportGenericMeasurableSingletons := by sorry
