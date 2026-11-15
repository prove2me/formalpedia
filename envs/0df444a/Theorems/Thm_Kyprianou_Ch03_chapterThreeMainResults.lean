-- Prove2me | Theorems.Thm_Kyprianou_Ch03_chapterThreeMainResults
-- name    : Kyprianou.Ch03.chapterThreeMainResults
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T16:44:26.239213+00:00
-- url     : https://prove2.me/theorems/92b7b25a-c193-408b-bd43-86e652668e70
-- title:
--   Chapter 3 complete conjunction of all thirteen certificates
-- statement:
--   The official main theorem is the conjunction of all thirteen complete quantified propositions of the Chapter 3 theorem, lemma and corollary items. Its proof entails every named theorem obligation. Definition 3.7 is separate.
-- source:
--   Kyprianou (2006), Chapter 3, pp. 67-82.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_ChapterCertification
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem chapterThreeMainResults :
  certificate_3_1 ∧
  certificate_3_2 ∧
  certificate_3_3 ∧
  certificate_3_4 ∧
  certificate_3_5 ∧
  certificate_3_6 ∧
  certificate_3_8 ∧
  certificate_3_9 ∧
  certificate_3_10 ∧
  certificate_3_11 ∧
  certificate_3_12 ∧
  certificate_3_13 ∧
  certificate_3_14 := by
  sorry

end Kyprianou.Ch03
