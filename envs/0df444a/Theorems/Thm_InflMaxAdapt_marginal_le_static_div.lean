-- Prove2me | Theorems.Thm_InflMaxAdapt_marginal_le_static_div
-- name    : InflMaxAdapt.marginal_le_static_div
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:21.859914+00:00
-- url     : https://prove2.me/theorems/70b95136-15f9-4aff-b7d7-eb5bf4a2758b
-- title:
--   Proof of Theorem 1 — the marginal gain over an optimal static set is at most $\mathbb E[\sigma(S)]/k$
-- statement:
--   In the undirected-edge representation with edge probabilities $q \in [0,1]$, let $k \ge 1$ and let $S$ be a set of $k$ seeds maximizing $\mathbb E[\sigma(S)]$, so that $\mathbb E[\sigma(S)] = \mathrm{Static}_k$. Then for every vertex $v \notin S$,
--   $$
--   \mathbb E\big[\sigma(S \cup \{v\}) - \sigma(S)\big] \;\le\; \frac{\mathbb E[\sigma(S)]}{k}.
--   $$
--   This is the step of the proof of Theorem 1 that converts the marginal terms of Lemma 4 into multiples of $\mathrm{Static}_k$.
--
--   Differences from the source:
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
--   - encoding: a set S of k seeds with E[σ(S)] = Static_k, and the quotient E[σ(S)]/k → hypotheses |S| = k, E[σ(S)] = Static_k and 1 ≤ k; reason: the quotient by k is undefined at k = 0, which the step excludes
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), proof of Theorem 1, printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeStatic

open MeasureTheory

namespace InflMaxAdapt

/-- The optimal-set marginal bound in the proof of Theorem 1 (printed p.6 = PDF p.7, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)),
in the undirected-edge representation: if `S` is a set of `k ≥ 1` seeds maximizing `E[σ(S)]`, so
`E[σ(S)] = Static_k`, then for every vertex `v ∉ S`,
`E[σ(S ∪ {v}) − σ(S)] ≤ E[σ(S)] / k`. -/
theorem marginal_le_static_div {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (S : Finset V) (hS : S.card = k) (hopt : edgeExpInfluence q S = edgeStatic q k)
    (v : V) (hv : v ∉ S) :
    edgeExpInfluence q (insert v S) - edgeExpInfluence q S ≤ edgeExpInfluence q S / k := by sorry

end InflMaxAdapt
