-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_lemma_6_4_edge_averages
-- name    : IsingLTL.FreeEntropy.lemma_6_4_edge_averages
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:14:27.471367+00:00
-- url     : https://prove2.me/theorems/217cd289-638b-41c3-bc02-b005d535536b
-- title:
--   Lemma 6.4 — $\frac1n\sum_{(i,j)\in E_n}F(B_{ij}(t))\to\frac{\bar P}{2}\mathbb E\{F(\bar T(\rho,t))\}$
-- statement:
--   Suppose a uniformly sparse graph sequence $\{G_n\}$ converges locally to the random tree $T(P,\rho,\infty)$. Fix $t\ge0$ and, for each $(i,j)\in E_n$, let $B_{ij}(t)$ be the subgraph of $G_n$ induced by the vertices at distance at most $t$ from $(i,j)$. Let $F$ be a fixed, bounded function on edge-rooted graphs with $F(T_1)=F(T_2)$ whenever $T_1\simeq T_2$. Then
--   $$\lim_{n\to\infty}\frac1n\sum_{(i,j)\in E_n}F(B_{ij}(t))=\frac{\bar P}{2}\,\mathbb E\{F(\bar T(\rho,t))\}.$$
--
--   Edge-local averages on the graph converge to their tree counterparts; the factor $\bar P/2$ is the limiting number of edges per vertex.
--
--   **Formalization Note** $\simeq$ is isomorphism of graphs carrying the (unordered) root edge to the root edge. $F$ is defined on all edge-rooted graphs, which is without loss. The sum over edges counts each edge once, written as half the sum over ordered adjacent pairs. Measurability of $F(\bar T(\rho,t))$ as a function of the two offspring functions is part of the conclusion.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 25, Lemma 6.4, (6.9)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_EdgeRooted

namespace IsingLTL.FreeEntropy

open MeasureTheory Filter Topology

/-- **Lemma 6.4** (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*, arXiv:0804.4726v3,
p. 25, eq. (6.9)). Suppose a uniformly sparse graph sequence `{G_n}` converges locally to the
random tree `T(P, ρ, ∞)`. Fixing a nonnegative integer `t`, for each `(i, j) ∈ E_n` denote by
`B_ij(t)` the subgraph of `G_n` induced by the vertices at distance at most `t` from `(i, j)`. Let
`F(·)` be a fixed, bounded function on the collection of all possible subgraphs that may occur as
`B_ij(t)`, such that `F(T₁) = F(T₂)` whenever `T₁ ≃ T₂`. Then
`lim_{n→∞} (1/n) ∑_{(i,j)∈E_n} F(B_ij(t)) = (P̄/2) E{F(T̄(ρ, t))}` (6.9).

Formalization Note.
1. `F` is a bounded function of an **edge-rooted graph** `(W, H, a, b)` (graph `H` on a type `W`
   with root edge endpoints `a, b`), invariant under graph isomorphisms carrying the root edge
   `{a, b}` to the root edge `{a', b'}` (unordered); this is the relation `≃` of p. 4 for graphs
   rooted at an edge. Defining `F` on all such graphs, not only on those occurring as `B_ij(t)`
   or as `T̄(ρ, t)`, is without loss (extend by `0` on the other isomorphism classes).
2. The sum over the edges `(i, j) ∈ E_n` (each counted once) is written as half the sum over
   ordered adjacent pairs, which is the same since `F(B_ij(t)) = F(B_ji(t))` by invariance.
3. `T̄(ρ, t)` is `edgeTreeBallGraph ω₁ ω₂ t` with `(ω₁, ω₂)` of law `rhoTree ⊗ rhoTree`: two
   independent trees `T(ρ, t)` whose roots are joined by the root edge `e` (pp. 24–25).
4. The conclusion includes measurability of `(ω₁, ω₂) ↦ F(T̄(t))` (it depends on finitely many
   offspring numbers), so the integral is the expectation and not a junk value. -/
theorem lemma_6_4_edge_averages (G : ∀ n : ℕ, SimpleGraph (Fin n)) [∀ n, DecidableRel (G n).Adj]
    (D : DegreeDist) (hsparse : UniformlySparse G) (hloc : ConvergesLocally G D) (t : ℕ)
    (F : (W : Type) → SimpleGraph W → W → W → ℝ)
    (hFbdd : ∃ C : ℝ, ∀ (W : Type) (H : SimpleGraph W) (a b : W), |F W H a b| ≤ C)
    (hFiso : ∀ (W₁ W₂ : Type) (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) (a₁ b₁ : W₁) (a₂ b₂ : W₂)
      (e : H₁ ≃g H₂), s(e a₁, e b₁) = s(a₂, b₂) → F W₁ H₁ a₁ b₁ = F W₂ H₂ a₂ b₂) :
    Measurable (fun ω : (List ℕ → ℕ) × (List ℕ → ℕ) =>
        F _ (edgeTreeBallGraph ω.1 ω.2 t) (edgeTreeLeft ω.1 ω.2 t) (edgeTreeRight ω.1 ω.2 t)) ∧
      Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n,
          if (G n).Adj i j then
            F _ (edgeBallGraph (G n) i j t) (edgeBallLeft (G n) i j t) (edgeBallRight (G n) i j t) / 2
          else 0)
        atTop
        (𝓝 (D.Pbar / 2 * ∫ ω : (List ℕ → ℕ) × (List ℕ → ℕ),
          F _ (edgeTreeBallGraph ω.1 ω.2 t) (edgeTreeLeft ω.1 ω.2 t) (edgeTreeRight ω.1 ω.2 t)
            ∂(D.rhoTree.prod D.rhoTree))) := by sorry

end IsingLTL.FreeEntropy
