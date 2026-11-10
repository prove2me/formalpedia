-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_6_5
-- name    : LoadBalMatch.Main.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:33:04.884615+00:00
-- url     : https://prove2.me/theorems/fdaca388-1345-4e08-873a-eaa9e7515362
-- title:
--   Lemma 6.5 — every fractional matching can be made succinct ($|\mathrm{supp}|\le 3n-1$) without changing loads or levels
-- statement:
--   Let $H$ be a graph on the finite set $V$ with $n=|V|$ and let $x\in P(H)$ be a fractional matching of $H$ (matching polytope with odd-set constraints). Then there is a fractional matching $z\in P(H)$ with the same load vector, the same level vector, and support of at most $3n-1$ edges:
--   $$z_v=x_v\ \text{ and }\ \ell^z_v=\ell^x_v\ \ (v\in V),\qquad |\operatorname{supp}(z)|\le 3n-1.$$
--   Here levels are taken in $H$: $\ell^x_v=\min_{u\in N_H(v)}x_u$ ($1$ at isolated vertices).
--
--   The paper calls a fractional matching **succinct** if its support has $O(n)$ edges; the lemma lets the algorithm store a balanced fractional matching in $O(n)$ words. The bound $3n-1$ is the one the proof derives (p. 28).
--
--   Differences from the source:
--   - generalization: succinct: the support has O(n) edges → |supp z| ≤ 3n − 1; reason: the proof (p. 28) shows an extreme point of Q has |supp| ≤ 3n − 1; this implies the O(n) claim with constant 3
--   - reading: any fractional matching can be made succinct without changing its load vector x(V) or level vector ℓ → there exists z ∈ P(H) with the same loads and the same levels (in H) as x and |supp z| ≤ 3n − 1; reason: the proof's construction: an extreme point of Q = {z ∈ P(G) : z_v = x_v ∀ v}
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 27, Lemma 6.5 (bound 3n − 1 from its proof, p. 28)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_FracMatching

namespace LoadBalMatch.Main

theorem lemma_6_5 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (x : Sym2 V → ℝ) (hx : IsFracMatching H x) :
    ∃ z : Sym2 V → ℝ, IsFracMatching H z ∧ (∀ v, load z v = load x v) ∧
      (∀ v, level H z v = level H x v) ∧ suppCard z ≤ 3 * Fintype.card V - 1 := by sorry

end LoadBalMatch.Main
