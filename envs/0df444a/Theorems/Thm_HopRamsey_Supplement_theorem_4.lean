-- Prove2me | Theorems.Thm_HopRamsey_Supplement_theorem_4
-- name    : HopRamsey.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:08:53.122278+00:00
-- url     : https://prove2.me/theorems/0f008a83-47a9-4e67-a66e-bacd36885256
-- title:
--   Theorem 4 (Distortion lower bound): Ramsey-type tree embeddings excluding $\varepsilon n$ vertices need distortion $\varepsilon^{-1}\Omega(\log(\varepsilon n))$
-- statement:
--   Let $\varepsilon>0$ be small. There is a connected graph $G=(V,E)$ with unit edge weights on $n$ vertices, for arbitrarily large $n$, such that every Ramsey-type embedding of $G$ into a tree that excludes at most $\varepsilon n$ vertices has distortion $\varepsilon^{-1}\cdot\Omega(\log(\varepsilon n))$.
--
--   Precisely: let $M\subseteq V$ with $|V\setminus M|\le\varepsilon n$, let $T$ be an arbitrary weighted tree with tree distance $d_T$, and let $f:V\to V(T)$ be **dominating** on $M$ with **distortion** $t$ on $M$:
--   $$d_G(u,v)\le d_T(f(u),f(v))\le t\cdot d_G(u,v)\qquad(u,v\in M),$$
--   where $d_G$ is the shortest-path distance of $G$. Then
--   $$t\ \ge\ c\cdot\varepsilon^{-1}\log(\varepsilon n),$$
--   where $c>0$ and the threshold $\varepsilon_0$ are absolute constants, fixed before $\varepsilon$, $n$ and $G$. The size of the witness is controlled as §5 claims ("$\varepsilon$ need not be a constant"): there are absolute $A$, $C_0$ such that for every $N_0$ with $\varepsilon N_0\ge C_0$ a witness exists with $N_0\le n\le A N_0$, so the bound covers the regime $\varepsilon=n^{-\Theta(1)}$.
--
--   This shows that the worst-case distortion $\varepsilon^{-1}\cdot\tilde O(\log n)$ of Theorem 1 is optimal up to lower-order factors even for arbitrary tree targets, and it matches the Ramsey-type upper bounds of Mendel–Naor and Filtser–Le.
--
--   **Formalization Note** Trees are `ARTreeCover.WGraph`s on an arbitrary type whose underlying graph is a Mathlib `SimpleGraph.IsTree`; the vertex set of $G$ is `Fin n`. The statement concerns a single deterministic embedding.
--
--   Differences from the source:
--   - reading: "For every small enough ε … (for arbitrarily large n) … distortion ε^{−1}·Ω(log(εn))", with the §5 opening (p.26) "ε need not be a constant … only require εN to be at least a sufficiently large constant; in particular, they cover the regime ε = N^{−Θ(1)}" → ∃ c > 0, ∃ ε₀ > 0, ∃ A, C₀, ∀ ε ∈ (0, ε₀], ∀ N₀ with ε·N₀ ≥ C₀, ∃ n with N₀ ≤ n ≤ A·N₀, ∃ G on Fin n: t ≥ c·ε⁻¹·log(εn), natural logarithm; reason: Ω(·) is a lower bound with an absolute constant (independent of ε and n, as in the proof); "for arbitrarily large n" is ∀ N₀ ∃ n ≥ N₀, and the size window [N₀, A·N₀] for every N₀ ≥ C₀/ε is the scope §5 claims for the theorem (it covers ε = N^{−Θ(1)}; taking N₀ large gives the plain reading); another fixed log base only rescales c
--   - generalization: an n-vertex graph G = (V,E,w) → a connected n-vertex graph with unit weight on every edge; reason: the proofs' witnesses are connected and unweighted (expanders, subdivided; p.12: unit weights); such a graph is a weighted graph, so the Lean statement implies the printed one, keeps the witness in the polynomial-weight regime of Theorem 1, and rules out the vacuous disconnected case (a finite tree distance cannot dominate d_G = ∞)
--   - generalization: a Ramsey-type embedding (p.13): dominating for all x, y ∈ V, distortion t for x ∈ M, y ∈ V → dominating and distortion t only for u, v ∈ M; reason: the proof takes "f : M → V(T) a dominating embedding … with distortion t" (p.30); weaker hypotheses bound a larger class, so the Lean statement implies the printed one
--   - encoding: a map f into an arbitrary weighted tree T → f : Fin n → W, T an ARTreeCover.WGraph on any type W whose graph is a Mathlib SimpleGraph.IsTree, tree distance T.dist; reason: a tree is nonempty, so a map on V constrained only on M is the same as a map on M; positive weights are the paper's convention (p.12)
--   - encoding: distortion t → a real t with d_T(f u, f v) ≤ ofReal(t)·d_G(u, v); reason: ofReal(t) = 0 for t ≤ 0; no instance changes
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §5.3, Theorem 4 (Distortion lower bound), p.30 (PDF p.32)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal

namespace HopRamsey

namespace Supplement

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §5.3,
Theorem 4 (Distortion lower bound), p.30 (PDF p.32): "For every small enough ε, there is an
n-vertex graph G = (V,E,w) (for arbitrarily large n) such that every Ramsey-type embedding f into a
tree with excluded set of size at most ε·n has distortion ε^{−1}·Ω(log(εn))."

There are absolute constants `c > 0`, `ε₀ > 0`, `A` and `C₀` such that for every `ε ∈ (0, ε₀]` and
every `N₀` with `ε N₀ ≥ C₀` there are `n` with `N₀ ≤ n ≤ A N₀` and a connected unweighted graph `G` on `n` vertices with the following property. Let
`M ⊆ V` be a saved set with `|V ∖ M| ≤ ε n`, `T` an arbitrary weighted tree, and `f : V → V(T)` a
map that is dominating on `M` (`d_G(u, v) ≤ d_T(f u, f v)` for `u, v ∈ M`) with distortion `t`
(`d_T(f u, f v) ≤ t · d_G(u, v)` for `u, v ∈ M`). Then `t ≥ c · ε⁻¹ · log(ε n)`.

**Formalization Note.**
1. "Ω(·)" is a lower bound with an absolute constant: `∃ c > 0` and `∃ ε₀ > 0` are chosen before
   `ε`, `n` and the graph. "For arbitrarily large n" is `∀ N₀, ∃ n ≥ N₀`, strengthened as the
   opening of §5 (p.26) says the proofs give: "ε need not be a constant: the proofs construct, from
   a base graph on n0 vertices, an instance with N = Θ(n0/ε) vertices, and only require εN to be at
   least a sufficiently large constant; in particular, they cover the regime ε = N^{−Θ(1)}". So
   there are absolute `A`, `C₀` such that for every `N₀` with `ε N₀ ≥ C₀` a witness exists with
   `N₀ ≤ n ≤ A N₀`; taking `N₀` large gives the plain "arbitrarily large n". `log` is the natural
   logarithm.
2. The witness graph is connected and unweighted (unit weight on every edge, p.12), as in the
   proofs. Connectedness is essential where the target is a tree: a tree distance is finite, so it
   cannot dominate `d_G = ∞` across components, and for a disconnected `G` the hypotheses would be
   unsatisfiable and the statement vacuous.
3. The tree `T` is an arbitrary weighted tree (`ARTreeCover.WGraph` on any type `W` whose graph is
   a Mathlib `SimpleGraph.IsTree`). The proof takes "f : M → V(T) a dominating embedding into an
   arbitrary weighted tree T with distortion t" (p.30), i.e. both conditions on `M × M`; a tree is
   nonempty, so a map `V → W` constrained only on `M` is the same thing. This bounds a larger class
   than the p.13 notion (dominating on `V × V`, distortion on `M × V`).
4. The theorem is about one deterministic embedding, not a distribution. -/
theorem theorem_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ A C₀ : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ N₀ : ℕ, C₀ ≤ ε * N₀ → ∃ n : ℕ, N₀ ≤ n ∧ (n : ℝ) ≤ A * N₀ ∧
      ∃ G : WGraph (Fin n), G.graph.Connected ∧ (∀ e ∈ G.graph.edgeSet, G.w e = 1) ∧
        ∀ M : Finset (Fin n), ((Finset.univ \ M).card : ℝ) ≤ ε * n →
        ∀ (W : Type) (T : WGraph W), T.graph.IsTree → ∀ (f : Fin n → W) (t : ℝ),
          (∀ u ∈ M, ∀ v ∈ M, G.dist u v ≤ T.dist (f u) (f v)) →
          (∀ u ∈ M, ∀ v ∈ M, T.dist (f u) (f v) ≤ ENNReal.ofReal t * G.dist u v) →
            c * ε⁻¹ * Real.log (ε * n) ≤ t := by sorry

end Supplement

end HopRamsey
