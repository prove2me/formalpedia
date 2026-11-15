-- Prove2me | Theorems.Thm_Kyprianou_Ch02_chapterTwoMainResults
-- name    : Kyprianou.Ch02.chapterTwoMainResults
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T11:30:37.749011+00:00
-- url     : https://prove2.me/theorems/a5c8e2b3-af4b-44b6-92c5-765031e5eb27
-- title:
--   Chapter 2 main results: Lévy–Itô decomposition and all supporting theorem obligations
-- statement:
--   A single conjunction certifying the full mathematical content of the seven supporting Chapter 2 theorem statements and Theorem 2.1. A proof must establish every conjunct. Each certificate is definitionally the universally quantified theorem proposition, not a shortcut proof or a weakened assumption.
-- source:
--   Kyprianou (2006), Chapter 2, pp. 33–66; source-faithful theorem statements in Chapter 2 draft.

import Definitions.Def_Kyprianou_Ch02_ChapterCertification
set_option autoImplicit false

theorem Kyprianou.Ch02.chapterTwoMainResults :
    Kyprianou.Ch02.certificate_poissonRandomMeasureExists ∧
    Kyprianou.Ch02.certificate_poissonRandomMeasureSupportCountable ∧
    Kyprianou.Ch02.certificate_poissonRandomMeasureIntegralLaws ∧
    Kyprianou.Ch02.certificate_largeJumpProcessLevy ∧
    Kyprianou.Ch02.certificate_compensatedBandIsL2Martingale ∧
    Kyprianou.Ch02.certificate_smallJumpLimitCadlag ∧
    Kyprianou.Ch02.certificate_sumOfIndependentLevyProcesses ∧
    Kyprianou.Ch02.certificate_levyItoDecomposition := by
  sorry
