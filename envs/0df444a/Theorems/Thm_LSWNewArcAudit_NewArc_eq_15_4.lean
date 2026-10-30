-- Prove2me | Theorems.Thm_LSWNewArcAudit_NewArc_eq_15_4
-- name    : LSWNewArcAudit.NewArc.eq_15_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:42:53.640899+00:00
-- url     : https://prove2.me/theorems/60c816eb-c263-4983-aec3-a5289b1dd404
-- title:
--   §15.2.2, equation (15.4) — decrease of one stable-frontloaded BFS
-- statement:
--   Let $f:2^V\to\mathbb Z$ be normalized and submodular, let $A$ be an acyclic directed graph, and let $\sigma$ be a supplied defining permutation consistent with $A$. Fix $p\in V$. There exists a permutation $\tau$ obtained by stably moving $R(p)$ to the front. For every such $\tau$, let $y$ and $y'$ be the BFSs defined by $\sigma$ and $\tau$. Then
--
--   $$y'(V\setminus R(p))-y(V\setminus R(p))\le y_p-\bigl(f(R(p))-f(R(p)\setminus\{p\})\bigr).$$
--
--   This is the entire per-BFS decrease display. It applies to each constituent of the source convex combination and supplies a bound on its outside-coordinate sum. Stable frontloading preserves relative order within both the moved set and its complement. The transformed BFS is computed by the same marginal formula, rather than selected to satisfy the desired bound.
--
--   Differences from the source:
--   - generalization: each BFS in the nondegenerate convex combination used in the proof of Lemma 79 → any individual BFS with a defining permutation consistent with the acyclic graph; reason: the displayed inequality depends only on that basis and its stable frontload, so every source basis is included without requiring weights or the trigger
--   - encoding: the permutation obtained by moving R(p) to the front → existence of a permutation satisfying the published stable-frontload relation, and the decrease inequality for every such permutation; reason: the relation fixes the entire resulting order, including the unchanged relative order outside R(p), and does not assume the inequality
--   - encoding: V=[n], coordinate sums and the integer difference upper(p) → Fin n, finite real sums and the real cast of the same integer difference; reason: reindexing changes no subset or value and real subtraction preserves the possibly negative decrease
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2 (5 Nov 2015), https://arxiv.org/pdf/1508.04874v2, §15.2.2, equation (15.4), printed/PDF p. 85, with standing assumptions §13.1 p. 74, Theorem 62 p. 76, Definition 74 p. 82.

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting

namespace LSWNewArcAudit.NewArc

open LSWCuttingPlane.SFMArcs

/-- Lee--Sidford--Wong, arXiv:1508.04874v2, §15.2.2, (15.4), p. 85.
The per-BFS outside-sum decrease for the actual stable-frontloaded permutation.
The formula uses real subtraction. No weighted-decrease bound is an assumption. -/
theorem eq_15_4 {n : ℕ} (f : Finset (Fin n) → ℤ)
    (hf : Submodular f) (hf0 : f ∅ = 0)
    (A : Fin n → Fin n → Prop) (hA : Acyclic A)
    (σ : Equiv.Perm (Fin n)) (hσ : Consistent A σ) (p : Fin n) :
    (∃ τ : Equiv.Perm (Fin n), IsFrontload σ (R A p) τ) ∧
    ∀ τ : Equiv.Perm (Fin n), IsFrontload σ (R A p) τ →
      ysum (bfs f τ) (Finset.univ \ R A p) -
          ysum (bfs f σ) (Finset.univ \ R A p) ≤
        bfs f σ p - (upper f A p : ℝ) := by sorry

end LSWNewArcAudit.NewArc
