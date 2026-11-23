-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_elementary_search_statistics
-- name    : IntegerRootsFN.Main.elementary_search_statistics
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:44.272792+00:00
-- url     : https://prove2.me/theorems/05df5957-317f-444e-9861-75d9b14d2435
-- title:
--   Elementary recursive search cardinality and total point size
-- statement:
--   For the actual elementary search output, the cardinality is at most $21d$ and its total point size is at most $21(5d+b+\frac12\log_2(d+1))$, where $d=\min(n,b)$. Following the second paragraph of Proposition A.3, after filtering to the final kept intervals, the intervals are pairwise separated by $2$. Lemma A.2 and Landau's bound imply each contains a root of the truncation and at most $7d$ roots are retained, giving at most $7d$ centres. Each raises `magnitudeLength` by at most one, the final step gives three integer candidates per centre, and deduplication can only improve both totals. The pre-final centres satisfy $\ell(m)+1\le5d+b+\frac12\log_2(d+1)-2$.
-- source:
--   Yansong Feng and Itamar Nir, STOC 2027 submission #1353 (October 2026), p.13, proof of Proposition A.3, second paragraph (at most $7d$ retained discs, at most $21d$ candidates and the total bit-size bound); uses Lemma A.2 on p.12 and Lemma 2.1 on p.5.

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch

set_option autoImplicit false

theorem IntegerRootsFN.Main.elementary_search_statistics :
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      (searchCandidates f n b).length ≤ 21 * min n b ∧
      (pointSize (searchCandidates f n b) : ℝ) ≤
        21 * (5 * (min n b : ℕ) + (b : ℝ) + (1 : ℝ) / 2 * logTwo ((min n b : ℕ) + 1)) := by sorry
