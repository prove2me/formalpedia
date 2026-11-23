-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_elementary_search_data
-- name    : IntegerRootsFN.Main.elementary_search_data
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:12:51.596458+00:00
-- url     : https://prove2.me/theorems/3936a2ec-c3ba-4420-a387-43f471fd1417
-- title:
--   Elementary recursive search: coverage, cardinality and total size
-- statement:
--   Let $n,b\ge1$ and let $f\in\mathbb Z[x]$ satisfy the standing degree and height promises. Put $d=\min(n,b)$ and let $C'$ be the exact list produced by the recursive scale search of Appendix A, including duplicate removal at the final scale.
--
--   Then every integer root $r$ of $f$ with $|r|\ge2$ belongs to $C'$, and
--
--   $$
--   |C'|\le21d,
--   $$
--
--   $$
--   \sum_{c\in C'}\lceil\log_2(2+|c|)\rceil
--    \le21\left(5d+b+\frac12\log_2(d+1)\right).
--   $$
--
--   The statement concerns the actual recursively defined search, rather than an existentially chosen set. Its proof uses the two semantic alternatives of Lemma A.2, truncation proximity from Lemma 2.2, and Landau's inequality. The finite-machine running time is a separate obligation.
--
--   **Formalization Note.** `pointSize` is the list sum of the individual magnitude lengths, and `searchCandidates` includes the final `eraseDups` operation.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 13, Proposition A.3, first three conclusions; proof uses p.12 Lemma A.2, p.3 Lemma 2.2 and p.3 Lemma 2.1.

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch

set_option autoImplicit false

theorem IntegerRootsFN.Main.elementary_search_data :
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      (∀ r : ℤ, f.IsRoot r → 2 ≤ |r| → r ∈ searchCandidates f n b) ∧
      (searchCandidates f n b).length ≤ 21 * min n b ∧
      (pointSize (searchCandidates f n b) : ℝ) ≤
        21 * (5 * (min n b : ℕ) + (b : ℝ) + (1 : ℝ) / 2 * logTwo ((min n b : ℕ) + 1)) := by sorry
