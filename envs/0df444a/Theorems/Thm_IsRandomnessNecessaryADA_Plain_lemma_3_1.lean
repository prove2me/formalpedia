-- Prove2me | Theorems.Thm_IsRandomnessNecessaryADA_Plain_lemma_3_1
-- name    : IsRandomnessNecessaryADA.Plain.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:17.191498+00:00
-- url     : https://prove2.me/theorems/d2e7548b-3bd1-4e72-bf7a-8787ea20723c
-- title:
--   Lemma 3.1 — one Boolean query separates every accurate branch
-- statement:
--   Let $n>0$, $N=20n$, and let $m$ be a deterministic natural mechanism over $[N]$. Let $T$ be a reachable transcript, meaning its replay-consistent set $H_T\subseteq[N]^n$ is nonempty. Take $P$ uniform on $[N]$. There exists one Boolean query $q$, chosen before the actual answer, such that for every real $a$,
--   $$|a-Pq|\le1/10\ \Longrightarrow\ |\{S\in H_T:m(S,T,q)=a\}|\le\tfrac9{10}|H_T|.$$
--   Thus every possible surviving actual sample either yields error strictly greater than $1/10$ or belongs to a branch shrinking the candidate set by at least one tenth. Queries whose every realized response is inaccurate are included. This is the separating-query lemma needed for the natural-mechanism attack, with the uniform guarantee over actual samples retained.
--
--   Differences from the source:
--   - encoding: one-based finite sets and ordered datasets → Fin indices and function tuples, with full real answers; reason: reindexing preserves every query, ordered sample with repetition, and response
--   - reading: a query either causes error or is separating → every accurate real-answer branch shrinks by at least one tenth, at every nonempty replay-consistent history; reason: §1.2.1 p.3 defines separation for valid answers and §4.4 p.12 uses precisely this rule
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), Lemma 3.1, p.8; §3 standing setup and proof, pp.8–9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Survivors

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

/-- Lemma 3.1, p.8, with its Section 3 standing setup and accurate-branch reading. -/
theorem lemma_3_1 (n : ℕ) (hn : 0 < n)
    (m : Mechanism (Fin (20 * n)) n) (hm : IsNatural m)
    (T : Transcript (StatisticalQuery (Fin (20 * n))))
    (hT : (survivors m T).Nonempty) :
    ∃ q : BooleanQuery (Fin (20 * n)),
      SeparatesAccurate m T (uniformFin (20 * n) (by omega)) (liftQuery q) := by sorry

end IsRandomnessNecessaryADA.Plain
