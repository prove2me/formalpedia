-- Prove2me | Theorems.Thm_Kyprianou_Ch10_Draft_result_10_14
-- name    : Kyprianou.Ch10.Draft.result_10_14
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:48:12.237047+00:00
-- url     : https://prove2.me/theorems/8076d112-3818-4620-9b51-943b4a9ac963
-- title:
--   Lemma 10.14: Conditional Lamperti correspondences, correcting the printed jump-sign error
-- statement:
--   State the forward and reverse conditional Lamperti correspondences with a spectrally positive Levy process, hence no negative jumps. The source on printed p.290 (physical PDF p.298) inadvertently says both spectrally positive and no positive jumps. The intended no-negative-jumps formulation is supported by Theorem 10.2 and the proof of Lemma 10.14. This is an expressly documented source erratum; the original mathematical theorem remains Open. Owner approved the documented no-negative-jumps correction on 19 November 2026; the original printed error remains cited.
-- source:
--   Kyprianou (2006), Chapter 10, Result 10.14; original physical PDF pages [298]. Original PDF SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf. ERRATUM: physical PDF p.298/printed p.290 literally says no positive jumps while also saying spectrally positive; mathematical intended no negative jumps, as in Theorem 10.2 and Lemma 10.14 proof. Independent R4 source-first review: literal source=>Lean REFUTED as entailment and Lean=>literal source PASS; corrected intended source=>Lean PASS and Lean=>source PASS. OWNER APPROVAL (19 November 2026): retain intended no-negative-jumps correction, documenting the literal no-positive-jumps printing.

import Definitions.Def_Kyprianou_Ch10_DraftSourceBundle
set_option autoImplicit false

theorem Kyprianou.Ch10.Draft.result_10_14 : Kyprianou.Ch10.StageD1Certificates.certLemma10_14 := by
  sorry
