-- Prove2me | Theorems.Thm_HopRamsey_Supplement_theorem_2
-- name    : HopRamsey.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:08:00.022209+00:00
-- url     : https://prove2.me/theorems/b9551949-be3a-4873-ba42-41fc03ddea89
-- title:
--   Theorem 2 (Hop-stretch lower bound): excluding $\varepsilon n$ vertices forces hop-stretch $\varepsilon^{-1}\Omega(\log(\varepsilon n))$
-- statement:
--   Let $\varepsilon>0$ be small. There is a connected graph $G=(V,E)$ with unit edge weights on $n$ vertices, for arbitrarily large $n$, such that no embedding of $G$ into any metric space can save all but an $\varepsilon$ fraction of the vertices with small hop-stretch.
--
--   Fix the hop parameter $h=1$, so that $d^{(1)}_G(u,v)$ is the edge weight when $\{u,v\}\in E$, $0$ when $u=v$, and $\infty$ otherwise, and $d^{(\beta)}_G(u,v)$ is the least weight of a $u$–$v$ path with at most $\beta$ edges. Let $(X,d_X)$ be any (extended, pseudo-) metric space, $f:V\to X$ any map and $M\subseteq V$ a saved set with $|V\setminus M|\le\varepsilon n$. Suppose $f$ has **finite distortion** on the saved vertices: for some real $t$,
--   $$d_X(f(u),f(v))\le t\cdot d^{(1)}_G(u,v)\qquad(u,v\in M).$$
--   If a natural number $\beta$ is a **hop-stretch** of $f$ on the saved vertices, that is $d^{(\beta)}_G(u,v)\le d_X(f(v),f(u))$ for all $u,v\in M$, then
--   $$\beta\ \ge\ c\cdot\varepsilon^{-1}\log(\varepsilon n).$$
--   Here $c>0$ and the threshold $\varepsilon_0$ ("small enough") are absolute constants, fixed before $\varepsilon$, $n$ and $G$. The size of the witness is controlled as §5 claims ("$\varepsilon$ need not be a constant"): there are absolute $A$, $C_0$ such that for every $N_0$ with $\varepsilon N_0\ge C_0$ a witness exists with $N_0\le n\le A N_0$, so the bound covers the regime $\varepsilon=n^{-\Theta(1)}$.
--
--   This shows that the hop-stretch $\varepsilon^{-1}\cdot\tilde O(\log n)$ of Theorem 1 is optimal up to lower-order factors, for every target metric and whatever the distortion.
--
--   **Formalization Note** Graphs are the published `ARTreeCover.WGraph` and $d^{(h)}_G$ is the published `HopRamsey.hopDist`; the vertex set is `Fin n`. Both conditions on $f$ are imposed only on saved pairs, which only enlarges the class of embeddings the bound applies to.
--
--   Differences from the source:
--   - reading: "For every small enough ε … (for arbitrarily large n) … hop-stretch β = ε^{−1}·Ω(log(εn))", with the §5 opening (p.26) "ε need not be a constant … only require εN to be at least a sufficiently large constant; in particular, they cover the regime ε = N^{−Θ(1)}" → ∃ c > 0, ∃ ε₀ > 0, ∃ A, C₀, ∀ ε ∈ (0, ε₀], ∀ N₀ with ε·N₀ ≥ C₀, ∃ n with N₀ ≤ n ≤ A·N₀, ∃ G on Fin n: β ≥ c·ε⁻¹·log(εn), natural logarithm; reason: Ω(·) is a lower bound with an absolute constant (independent of ε and n, as in the proof); "for arbitrarily large n" is ∀ N₀ ∃ n ≥ N₀, and the size window [N₀, A·N₀] for every N₀ ≥ C₀/ε is the scope §5 claims for the theorem (it covers ε = N^{−Θ(1)}; taking N₀ large gives the plain reading); another fixed log base only rescales c
--   - reading: hop-stretch with an unspecified hop parameter → hop parameter h = 1, so d^{(β·h)}_G = d^{(β)}_G and distortion is measured against d^{(1)}_G; reason: the proof fixes h = 1 ("Fix h = 1", p.26); the theorem asserts the existence of such a G
--   - generalization: an n-vertex graph G = (V,E,w) → a connected n-vertex graph with unit weight on every edge; reason: the proofs' witnesses are connected and unweighted (expanders, subdivided; p.12: unit weights); such a graph is a weighted graph, so the Lean statement implies the printed one, keeps the witness in the polynomial-weight regime of Theorem 1, and rules out the vacuous disconnected case (a finite tree distance cannot dominate d_G = ∞)
--   - generalization: hop-stretch for all u, v ∈ V and distortion for u ∈ M, v ∈ V (Definition 2) → both conditions only for u, v ∈ M; reason: the proof uses both only on saved pairs (the component C and the path in G′ ∖ R); weaker hypotheses bound a larger class of embeddings, so the Lean statement implies the printed one
--   - generalization: an arbitrary metric (X, d_X) → any type X with a PseudoEMetricSpace structure (distances in [0, ∞], distinct points may be at distance 0); reason: every metric space, and the ∞-valued metrics the paper allows (p.12), are instances
--   - encoding: finite distortion → ∃ t : ℝ with d_X(f u, f v) ≤ ofReal(t)·d^{(1)}_G(u, v) for saved u, v; reason: ofReal(t) = 0 for t ≤ 0 only imposes stronger conditions, so the class equals the one with t > 0
--   - encoding: hop-stretch β → a natural number β; d^{(h)}_G is the published HopRamsey.hopDist (infimum over walks with at most h edges, in [0, ∞]); reason: d^{(β·h)} is defined for integer hop counts; walks and paths give the same value for positive weights
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §5.1, Theorem 2 (Hop-stretch lower bound), p.26 (PDF p.28)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_hopDist

open scoped ENNReal

namespace HopRamsey

namespace Supplement

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §5.1,
Theorem 2 (Hop-stretch lower bound), p.26 (PDF p.28): "For every small enough ε, there is an
n-vertex graph G = (V,E,w) (for arbitrarily large n) such that every finite-distortion embedding f
into an arbitrary metric (X,d_X) that excludes at most an ε fraction of the vertices has hop-stretch
β = ε^{−1}·Ω(log(εn))."

There are absolute constants `c > 0`, `ε₀ > 0`, `A` and `C₀` such that for every `ε ∈ (0, ε₀]` and
every `N₀` with `ε N₀ ≥ C₀` there are `n` with `N₀ ≤ n ≤ A N₀` and a connected unweighted graph `G` on `n` vertices with the following property. With
hop parameter `h = 1`, let `f : V → X` be any map into any (pseudo-extended) metric space `X` and
`M ⊆ V` any saved set with `|V ∖ M| ≤ ε n`, such that `f` has finite distortion
(`d_X(f u, f v) ≤ t · d^{(1)}_G(u, v)` for some real `t` and all saved `u, v`). Then every natural
number `β` that is a hop-stretch of `f` (`d^{(β)}_G(u, v) ≤ d_X(f v, f u)` for all saved `u, v`)
satisfies `β ≥ c · ε⁻¹ · log(ε n)`.

**Formalization Note.**
1. "Ω(·)" is a lower bound with an absolute constant: `∃ c > 0` and `∃ ε₀ > 0` are chosen before
   `ε`, `n` and the graph. "For arbitrarily large n" is `∀ N₀, ∃ n ≥ N₀`, strengthened as the
   opening of §5 (p.26) says the proofs give: "ε need not be a constant: the proofs construct, from
   a base graph on n0 vertices, an instance with N = Θ(n0/ε) vertices, and only require εN to be at
   least a sufficiently large constant; in particular, they cover the regime ε = N^{−Θ(1)}". So
   there are absolute `A`, `C₀` such that for every `N₀` with `ε N₀ ≥ C₀` a witness exists with
   `N₀ ≤ n ≤ A N₀`; taking `N₀` large gives the plain "arbitrarily large n". `log` is the natural
   logarithm (another fixed base only changes `c`).
2. The hop parameter is `h = 1`, the proof's choice ("Fix h = 1", p.26), so `d^{(β·h)}_G = d^{(β)}_G`.
3. The witness graph is connected and unweighted (unit weight on every edge, p.12), as in the
   proof (a subdivided constant-degree expander); both properties only strengthen the statement.
4. Both the distortion and the hop-stretch conditions are required only on saved pairs, which is
   what the proof uses; Definition 2 requires hop-stretch on all pairs and distortion on `M × V`,
   so the statement here bounds a larger class of embeddings.
5. The target is any `PseudoEMetricSpace`: every metric space, and metrics taking the value `∞`
   (p.12) or identifying points, are included. -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ A C₀ : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ N₀ : ℕ, C₀ ≤ ε * N₀ → ∃ n : ℕ, N₀ ≤ n ∧ (n : ℝ) ≤ A * N₀ ∧
      ∃ G : WGraph (Fin n), G.graph.Connected ∧ (∀ e ∈ G.graph.edgeSet, G.w e = 1) ∧
        ∀ (X : Type) [PseudoEMetricSpace X] (f : Fin n → X) (M : Finset (Fin n)),
          ((Finset.univ \ M).card : ℝ) ≤ ε * n →
          (∃ t : ℝ, ∀ u ∈ M, ∀ v ∈ M, edist (f u) (f v) ≤ ENNReal.ofReal t * hopDist G 1 u v) →
          ∀ β : ℕ, (∀ u ∈ M, ∀ v ∈ M, hopDist G β u v ≤ edist (f v) (f u)) →
            c * ε⁻¹ * Real.log (ε * n) ≤ (β : ℝ) := by sorry

end Supplement

end HopRamsey
