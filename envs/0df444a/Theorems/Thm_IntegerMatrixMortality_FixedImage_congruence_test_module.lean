-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_congruence_test_module
-- name    : IntegerMatrixMortality.FixedImage.congruence_test_module
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:17.417112+00:00
-- url     : https://prove2.me/theorems/2ccc24a4-cade-4734-b7ef-38291bcb9b7e
-- title:
--   Lemma C.2 — Congruence-test module
-- statement:
--   Fix d≥1 and A⊆{0,…,d−1}. The concrete graph (C.2) satisfies all three module requirements for every prime p≥7, and implements precisely the partial identity
--
--   $$z_n\longmapsto z_n\quad\text{when }n\bmod d\in A.$$
--
--   It has exactly 1+d+|A|+1_{0∈A} listed generators. Both d=1 and A=∅ are covered, and every valid unfinished prefix obeys the residue requirement.
--
--   Differences from the source:
--   - encoding: a concrete finite source module with private phases → the corresponding named finite edge list, with all three requirements asserted; reason: local labels are renamed privately for each occurrence, including coincident program boundaries
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma C.2, PDF p. 21 / printed p. 19

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem congruence_test_module
    (d : ℕ) (A : Finset ℕ) (hd : 1 ≤ d) (hA : ∀ a ∈ A, a < d) :
      ModuleRequirements (testModule d A) (instructionUpdate (.test d A)) ∧
      (testModule d A).edges.length = 1+d+A.card+(if 0 ∈ A then 1 else 0) := by sorry

end IntegerMatrixMortality.FixedImage
