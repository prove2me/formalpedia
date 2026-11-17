-- Prove2me | Theorems.Thm_HopRamsey_Supplement_theorem_3
-- name    : HopRamsey.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:08:31.868714+00:00
-- url     : https://prove2.me/theorems/6a80b0f1-dc20-4391-8f80-97ca91bcfdba
-- title:
--   Theorem 3 (Expected distortion with exclusion probability lower bound): $\Omega(\log n)$ for stochastic tree embeddings
-- statement:
--   Let $\varepsilon>0$ be small. There is a connected graph $G=(V,E)$ with unit edge weights on $n$ vertices, for arbitrarily large $n$, such that every stochastic embedding of $G$ into trees with exclusion probability $\varepsilon$ has expected distortion $\Omega(\log n)$.
--
--   Precisely: let $(\Omega,\mu)$ be a probability space and, for each sample $\omega$, let $T_\omega$ be a weighted tree with a map $f_\omega:V\to T_\omega$ and a saved set $M_\omega\subseteq V$ (measurable in $\omega$). Assume almost surely that the embedding is **dominating** on saved pairs, $d_G(u,v)\le d_{T_\omega}(f_\omega(u),f_\omega(v))$ for $u,v\in M_\omega$, where $d_G$ is the shortest-path distance. Assume the **exclusion probability** is at most $\varepsilon$, i.e. $\Pr[v\notin M]\le\varepsilon$ for every $v\in V$, and the **expected distortion** is at most $t$:
--   $$\mathbb E\big[d_{T}(f(u),f(v))\cdot\mathbf 1_{u,v\in M}\big]\le t\cdot d_G(u,v)\qquad(u,v\in V).$$
--   Then
--   $$t\ \ge\ c\cdot\log n,$$
--   where $c>0$ and the threshold $\varepsilon_0$ are absolute constants, fixed before $\varepsilon$, $n$ and $G$. Hop constraints play no role.
--
--   This shows that the expected distortion $\tilde O(\log n)$ of Theorem 1 cannot be improved, even for arbitrary tree targets and even though each vertex may be dropped with probability $\varepsilon$; it extends Bartal's $\Omega(\log n)$ lower bound for stochastic tree embeddings.
--
--   **Formalization Note** A sample is recorded by its pulled-back distance $d_\omega(u,v)=d_{T_\omega}(f_\omega(u),f_\omega(v))$, required almost surely to be a tree metric (`HopRamsey.Supplement.IsTreeMetric`); trees are `ARTreeCover.WGraph`s on an arbitrary type whose graph is a Mathlib tree. The expectation is a lower Lebesgue integral in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: "For every small enough ε … (for arbitrarily large n) … expected distortion Ω(log n)" → ∃ c > 0, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀], ∀ N₀, ∃ n ≥ N₀, ∃ G on Fin n: t ≥ c·log n, natural logarithm; reason: Ω(·) is a lower bound with an absolute constant (independent of ε and n, as in the proof); "for arbitrarily large n" is ∀ N₀ ∃ n ≥ N₀; another fixed log base only rescales c
--   - generalization: an n-vertex graph G = (V,E,w) → a connected n-vertex graph with unit weight on every edge; reason: the proofs' witnesses are connected and unweighted (expanders, subdivided; p.12: unit weights); such a graph is a weighted graph, so the Lean statement implies the printed one, keeps the witness in the polynomial-weight regime of Theorem 1, and rules out the vacuous disconnected case (a finite tree distance cannot dominate d_G = ∞)
--   - generalization: a distribution over dominating embeddings into trees → any probability measure μ on any measurable sample space Ω, with almost every sample a tree metric that dominates d_G on its saved pairs; reason: the proof uses domination only on saved pairs; every discrete distribution is an instance (Ω its sample type), and a.e. conditions are weaker than conditions on every sample
--   - encoding: a distribution (probabilities and expectations) → measurability of ω ↦ d_ω(u, v) and of the events {v ∈ M_ω}; expectation as a lower Lebesgue integral in [0, ∞]; reason: makes Pr[v ∉ M] and E[d_{T,M}(u, v)] the usual probability and expectation; every distribution in the paper has these
--   - encoding: an embedding into a tree T → the pulled-back distance d_T(f u, f v), T an ARTreeCover.WGraph on any type W whose graph is a Mathlib SimpleGraph.IsTree; reason: every property in the theorem reads only these distances; positive edge weights are the paper's convention (p.12)
--   - encoding: expected distortion of Definition 2 with d^{(h)}_G → expected distortion against the shortest-path distance d_G (published ARTreeCover.WGraph.dist); reason: the theorem "completely disregards hop constraints" (p.27); it concerns classical stochastic tree embeddings (p.13)
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §5.2, Theorem 3 (Expected distortion with exclusion probability lower bound), p.27 (PDF p.29)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_Supplement_IsStochTreeEmbedding

open scoped ENNReal
open MeasureTheory

namespace HopRamsey

namespace Supplement

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §5.2,
Theorem 3 (Expected distortion with exclusion probability lower bound), p.27 (PDF p.29): "For every
small enough ε, there is an n-vertex graph G = (V,E,w) (for arbitrarily large n) such that every
stochastic embedding of G into trees with exclusion probability ε has expected distortion
Ω(log n)."

There are absolute constants `c > 0` and `ε₀ > 0` such that for every `ε ∈ (0, ε₀]` and every `N₀`
there are `n ≥ N₀` and a connected unweighted graph `G` on `n` vertices such that every stochastic
dominating embedding of `G` into trees (`IsStochTreeEmbedding`) with exclusion probability `ε`
(`Pr[v ∉ M] ≤ ε` for every `v`) and expected distortion `t`
(`E[d_T(u, v) · 1_{u, v ∈ M}] ≤ t · d_G(u, v)` for all `u, v`) has `t ≥ c · log n`.

**Formalization Note.**
1. "Ω(·)" is a lower bound with an absolute constant: `∃ c > 0` and `∃ ε₀ > 0` are chosen before
   `ε`, `n` and the graph. "For arbitrarily large n" is `∀ N₀, ∃ n ≥ N₀`. `log` is the natural
   logarithm.
2. Hop constraints play no role ("This theorem completely disregards hop constraints", p.27): all
   distances are shortest-path distances `d_G`.
3. The witness graph is connected and unweighted (unit weight on every edge, p.12), as in the
   proof. Connectedness is essential where the target is a tree: a tree distance is finite, so it
   cannot dominate `d_G = ∞` across components, and for a disconnected `G` the hypotheses would be
   unsatisfiable and the statement vacuous.
4. The distribution is any probability measure on any measurable sample space with measurable
   samples; the trees are arbitrary weighted trees; domination is required on saved pairs only
   (see `IsStochTreeEmbedding`). -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      ∃ G : WGraph (Fin n), G.graph.Connected ∧ (∀ e ∈ G.graph.edgeSet, G.w e = 1) ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (d : Ω → Fin n → Fin n → ℝ≥0∞)
          (M : Ω → Finset (Fin n)) (t : ℝ),
          IsStochTreeEmbedding G μ d M → HasExclusionProb μ M ε →
          HasExpectedDistortion G μ d M t →
            c * Real.log n ≤ t := by sorry

end Supplement

end HopRamsey
