-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_exact_interval_representation
-- name    : MatchingNearLinear.Glauber.Supplement.exact_interval_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:00:49.781292+00:00
-- url     : https://prove2.me/theorems/745869ae-e838-41a5-97fc-6bb7c89f945e
-- title:
--   Lemma 5.2 — Exact interval representation
-- statement:
--   Let $G$ be a labeled simple graph with $n$ vertices and $m$ edges, let $M_0$ be a matching of $G$, and let $(e_s,B_s)_{s=1}^T$ be any fixed update tape (fixed edges and fixed marks; no randomness). Let $M_t$ be the sequential single-edge GD state after $t$ updates from $M_0$, and let $\mathcal A$ be the set of records accepted by the occupation-interval peeling algorithm on this tape and $M_0$. Then for every $t\in\{0,1,\dots,T\}$,
--   $$\{e:\ (e,[s,d))\in\mathcal A,\ s\le t<d\}\;=\;M_t .$$
--
--   That is, ordered parallel peeling reproduces every state of the sequential GD trajectory, not only the final one. This is the correctness half of the work-efficient parallel simulation (Theorem 5.1).
--
--   Differences from the source:
--
--   - generalization: one batch of T ≤ m updates on a graph with m ≥ 1 edges (§5.1 context) → any tape length T and any m; reason: the lemma is pathwise for every fixed update sequence and its argument uses neither bound; it specializes to T ≤ m, m ≥ 1
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma 5.2, printed p. 23 (PDF p. 25); algorithm §5.1, printed pp. 22–23 (PDF pp. 24–25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_Peeling

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem exact_interval_representation (n m T : ℕ) (G : Input n m) (M0 : Config m)
    (hM0 : EdmondsMatching65.Polyhedron.IsMatching G.graph M0)
    (tape : Fin T → Fin m × Bool) :
    ∀ t ≤ T, peelState G M0 tape t = gdState G M0 tape t := by sorry

end MatchingNearLinear.Glauber.Supplement
