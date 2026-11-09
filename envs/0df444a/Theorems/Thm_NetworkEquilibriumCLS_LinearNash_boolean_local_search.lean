-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_boolean_local_search
-- name    : NetworkEquilibriumCLS.LinearNash.boolean_local_search
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:55.312552+00:00
-- url     : https://prove2.me/theorems/620e6ce1-4f67-48a0-9b15-316e998c567c
-- title:
--   Lemma 3.2 — Boolean bilinear local-search alternative
-- statement:
--   Given any rational quadratic p on [0,1]^m, one can construct an integer square-free quadratic h on {0,1}^n in polynomial time, together with a uniform polynomial-time decoder D_p, such that
--
--   $$h(b)\le h(b\oplus q)\text{ for all }q\quad\Longrightarrow\quad D_p(b)\text{ is an exact KKT point of }p.$$
--
--   The dimension n varies with the source instance. The encoded target accepts every single-flip local minimum and the decoder must work for all of them. The polynomial h is the same polynomial later extended to the real domain. This supplies the Boolean alternative used in Section 4.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: a finite Boolean dimension n → n>0, with an unused variable available when a reduction would produce zero variables; reason: padding an empty Boolean instance by one irrelevant coordinate preserves every local minimum and its decoded source point, without a new source hypothesis
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.9 (PDF 10), Lemma 3.2.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_BooleanSearch

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem boolean_local_search :
    SearchReduces quadraticSearch booleanSearch := by sorry

end NetworkEquilibriumCLS.LinearNash
