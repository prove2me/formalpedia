-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_4
-- name    : LocalProbeMIS871.Greedy.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:53:33.878104+00:00
-- url     : https://prove2.me/theorems/d2972ff2-fd14-4720-9114-10494793c508
-- title:
--   Lemma 3.4 — Evaluations in a residual graph
-- statement:
--   Let $G$ be a finite simple undirected labeled graph, let $v$ be its fixed query root, and use the cached, early-stopping greedy evaluation. Write $R$ for its fresh evaluated vertices, $U=|R|$, $\tau(u)$ for elimination times, $M_s=\sum_{u\in R}\tau(u)^s$, $X=\sum_{u\in R\setminus\{v\}}\tau(u)^s$, $D=\sum_{u\in R\setminus\{v\}}\tau(u)^s\ln(r(u)/\tau(u))$, and $c_s=\ln(s-1)-1$. Unless stated otherwise below, the root has rank $1$ and the other ranks are independent uniforms on $(0,1)$.
--
--   For every distinct-rank realization with root rank $1$ and every $0\le t<1$, let $H_t$ be the graph induced by vertices with $\tau(u)>t$. Then
--
--   $$R_G(v,r)\cap V(H_t)=R_{H_t}(v,r|_{V(H_t)}),$$
--
--   where the right side is empty when $v$ is absent.
--
--   This identity identifies the remaining evaluations with a query in the actual residual graph.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: query in H_t with empty set for absent root → a run on the induced subtype, mapped back to original labels, with an explicit empty branch; reason: the root is never fabricated when it is absent
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 13, PDF p. 15, Lemma 3.4, Eq.(10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Lemma 3.4, printed p.13 / PDF15, including the absent-root convention. -/
theorem lemma_3_4 {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (r : Fin n → ℝ) (hr : GoodRanks v r) (t : ℝ) (ht : 0 ≤ t ∧ t < 1) :
    P G v r t = residualR G v r t := by sorry

end LocalProbeMIS871.Greedy
