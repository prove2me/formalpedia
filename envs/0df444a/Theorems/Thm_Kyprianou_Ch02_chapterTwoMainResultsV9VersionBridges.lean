-- Prove2me | Theorems.Thm_Kyprianou_Ch02_chapterTwoMainResultsV9VersionBridges
-- name    : Kyprianou.Ch02.chapterTwoMainResultsV9VersionBridges
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T10:21:43.350116+00:00
-- url     : https://prove2.me/theorems/f3de990b-f851-47bb-b3eb-98dd37eac78a
-- title:
--   Chapter 2 V9 version bridge obligations
-- statement:
--   The conjunction of the five Chapter 2 certificate obligations introduced or repaired after the V5 aggregate: the V6 marked compound-Poisson random measure result, the two V9 generic abstract Poisson-random-measure results, the V6 form of Exercise 2.2, and the V5 measurable-singleton support result.
-- source:
--   Kyprianou (2006), Chapter 2 pp. 33-66; cumulative V9 certificate alignment

import Mathlib
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV9
open MeasureTheory ProbabilityTheory Kyprianou
set_option autoImplicit false

theorem Kyprianou.Ch02.chapterTwoMainResultsV9VersionBridges :
    Kyprianou.Ch02.certificateV6_markedCompoundPoissonRandomMeasureCh02V6 ∧
    Kyprianou.Ch02.certificateV9_poissonRandomMeasureExistsGenericCh02V9 ∧
    Kyprianou.Ch02.certificateV9_poissonRestrictionAndIndependenceGenericCh02V9 ∧
    Kyprianou.Ch02.certificateV6_exercise2_2_AllPartsCh02V6 ∧
    Kyprianou.Ch02.certificateV5_poissonRandomMeasureSupportGenericMeasurableSingletons := by sorry
