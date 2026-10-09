-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_lemma_4_4
-- name    : LinearPathTuran.Exact.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:12.956253+00:00
-- url     : https://prove2.me/theorems/8aa6ce8e-52f6-4e84-ae97-38c74fb34d24
-- title:
--   Lemma 4.4 (Erdős–Gallai) — an n-vertex graph with no cycle of length ≥ c has at most (c−1)(n−1)/2 edges
-- statement:
--   **Erdős–Gallai circumference theorem.** Let $c\ge 3$. If $G$ is a graph on $n$ vertices that contains no cycle of length at least $c$, then
--   $$e(G)\le\tfrac12(c-1)(n-1).$$
--
--   In the paper it bounds the number of edges of the centre graph $H'$, whose circumference is at most $2t$ for a $\mathbb P_{2t+2}^{(k)}$-free family (Claim 1 of Theorem 4.5).
--
--   **Formalization Note** $G$ is a simple graph on `Fin n`; "no cycle of length at least $c$" says every cycle has length less than $c$. The factor $\tfrac12$ is cleared: the statement is $2e(G)\le(c-1)(n-1)$, with natural-number subtraction $n-1$ (both sides are $0$ for $n\le1$). The lemma is cited from Erdős and Gallai (1959).
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 8, Lemma 4.4 (cited from Erdős and Gallai, On maximal paths and circuits of graphs, Acta Math. Acad. Sci. Hungar. 10 (1959))

import Mathlib

namespace LinearPathTuran.Exact

open Finset

/-- Lemma 4.4 (Erdős–Gallai), p. 8: an `n`-vertex graph with no cycle of length at least `c ≥ 3`
has at most `(c - 1)(n - 1)/2` edges. -/
theorem lemma_4_4 (n c : ℕ) (hc : 3 ≤ c) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → p.length < c) :
    2 * #G.edgeFinset ≤ (c - 1) * (n - 1) := by sorry

end LinearPathTuran.Exact
