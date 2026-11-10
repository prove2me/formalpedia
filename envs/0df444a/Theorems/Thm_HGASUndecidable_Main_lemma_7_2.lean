-- Prove2me | Theorems.Thm_HGASUndecidable_Main_lemma_7_2
-- name    : HGASUndecidable.Main.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:16:54.258466+00:00
-- url     : https://prove2.me/theorems/be2e16bf-34e2-4ca8-a688-a9376f50c9d8
-- title:
--   Lemma 7.2 — fixed Diophantine system A n∘² + B n = c0 + e c1 (nonzero columns of B) solvable iff e ∈ K
-- statement:
--   Lemma 7.2 (A fixed Diophantine equation). There are integers q, r ≥ 1, matrices A∗, B∗ ∈ Z^{r×q} and vectors c0, c1 ∈ Z^r such that every column of B∗ is nonzero and, with c(e) = c0 + e c1, e ∈ K ⇐⇒ ∃n ∈ Z^q : A∗n^{◦2} + B∗n = c(e), e ∈ N. (7.2)
--
--   Differences from the source:
--   - encoding: the halting set of a universal Turing machine on paired input → definedness of (Nat.Partrec.Code.ofNatCode e.unpair.1).eval e.unpair.2; reason: this is the universal partial-recursive halting problem, with the same many-one completeness convention
--   - encoding: integer matrices and vectors q,r,A,B,c₀,c₁ → one record DiophantineData with finite zero-based matrix indices; reason: existence of this record is exactly simultaneous existence of the displayed data
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Lemma 7.2, printed p. 36 (PDF 38)

import Definitions.Def_HGASUndecidable_Main_Fourier

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem lemma_7_2 : ∃ a : DiophantineData, DiophantineValid a := by sorry

end HGASUndecidable.Main
