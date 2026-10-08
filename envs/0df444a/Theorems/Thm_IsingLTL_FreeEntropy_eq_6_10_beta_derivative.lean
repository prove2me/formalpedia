-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_eq_6_10_beta_derivative
-- name    : IsingLTL.FreeEntropy.eq_6_10_beta_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:09.47903+00:00
-- url     : https://prove2.me/theorems/b96c0064-c2b1-4709-87d6-90f9916402e4
-- title:
--   (6.10) — $\partial_\beta\phi_n(\beta,B)=\frac1n\sum_{(i,j)\in E_n}\langle x_ix_j\rangle_n$
-- statement:
--   Let $G=(V,E)$ be a finite graph with $n=|V|$ vertices and $\langle\cdot\rangle_n$ the expectation under the Ising measure (1.1) on $G$ at parameters $\beta$ and $B$. Then $\beta\mapsto\phi_n(\beta,B)$ is differentiable and
--   $$\partial_\beta\phi_n(\beta,B)=\frac1n\sum_{(i,j)\in E}\langle x_ix_j\rangle_n.$$
--
--   This identity reduces the free entropy density to expectations of local quantities.
--
--   **Formalization Note** Stated for every finite graph, every $\beta\in\mathbb R$ and every constant field $B$. The edge sum counts each edge once, written as half the sum over ordered adjacent pairs.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 26, (6.10), in the proof of Theorem 2.4

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_PartitionFunction

namespace IsingLTL.FreeEntropy

/-- **Equation (6.10)** (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*,
arXiv:0804.4726v3, p. 26, in the proof of Theorem 2.4). Denoting by `⟨·⟩_n` the expectation with
respect to the Ising measure on `G_n` (at parameters `β` and `B`),
`∂_β φ_n(β, B) = (1/n) ∑_{(i,j)∈E_n} ⟨x_i x_j⟩_n` (6.10).

Formalization Note: stated for every finite graph `G` on a vertex type `V` with `n = |V|`, every
`β` and every constant field `B`, as `HasDerivAt` (which asserts differentiability too). The sum
over edges (each counted once) is half the sum over ordered adjacent pairs. At `n = 0` both sides
are `0`. -/
theorem eq_6_10_beta_derivative {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β B : ℝ) :
    HasDerivAt (fun b : ℝ => freeEntropyDensity G b B)
      ((∑ i : V, ∑ j : V, if G.Adj i j then
          pairing (isingOn G β (fun _ => B) ∅ Finset.univ)
            (fun x => spinOf Finset.univ x i * spinOf Finset.univ x j) / 2 else 0)
        / Fintype.card V) β := by sorry

end IsingLTL.FreeEntropy
