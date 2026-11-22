-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneV4_last33_part_b2
-- name    : Kyprianou.Ch01.chapterOneV4_last33_part_b2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:31:41.868655+00:00
-- url     : https://prove2.me/theorems/a7a37921-b1a3-4a49-902b-4776dc6e1e15
-- title:
--   Exact Chapter 1 V4 certificates 51–56 of 67
-- statement:
--   Conjunction of exact source-faithful V4 certificates 51–56 of 67, including all original hypotheses, universe parameters and moderator boundary repairs. The b1 and b2 certificates together reconstruct the original eleven-clause child b.
-- source:
--   Kyprianou (2006), Chapter 1 V4 67-result root.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneV4_last33_part_b2 :
    Kyprianou.Ch01.certificate_branchingOneAncestorGeneratorFromRates ∧
    Kyprianou.Ch01.certificate_levyTripletExponentSignBridgeReviewed ∧
    Kyprianou.Ch01.certificate_continuousRepresentativeForAlmostSurePaths.{u} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess.{u} := by
  sorry
