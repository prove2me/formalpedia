-- Prove2me | Theorems.Thm_Kyprianou_Ch02_chapterTwoMainResultsV5
-- name    : Kyprianou.Ch02.chapterTwoMainResultsV5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T18:38:35.260379+00:00
-- url     : https://prove2.me/theorems/daeda418-3979-4916-923e-f72ee7907133
-- title:
--   Chapter 2 V5: 30 corrected source result certificates
-- statement:
--   Source-faithful cumulative conjunction of all thirty Chapter 2 milestones, including Exercises 2.1–2.12. Replaces only the deprecated Corollary 2.6 general-space singleton-support assertion with its sound measurable-singleton interface, retaining the other twenty-nine V4 result certificates without changes.
-- source:
--   Kyprianou (2006) Chapter 2 pp. 33-66, solutions pp. 307-311; ISS-0053 and owner V4 repair

import Mathlib
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV2
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV5
open MeasureTheory ProbabilityTheory Kyprianou
set_option autoImplicit false

theorem Kyprianou.Ch02.chapterTwoMainResultsV5 :
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
    Kyprianou.Ch02.certificateV4_markedCompoundPoissonRandomMeasureCh02V5 ∧
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
    Kyprianou.Ch02.certificateV4_exercise2_2_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV3_exercise2_7_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_10_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV3_exercise2_5_AllPartsCh02V3 ∧
    Kyprianou.Ch02.certificateV4_exercise2_9_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV4_exercise2_12_AllPartsCh02V4 ∧
    Kyprianou.Ch02.certificateV5_poissonRandomMeasureSupportGenericMeasurableSingletons := by sorry
