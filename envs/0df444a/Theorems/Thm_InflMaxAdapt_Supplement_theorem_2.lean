-- Prove2me | Theorems.Thm_InflMaxAdapt_Supplement_theorem_2
-- name    : InflMaxAdapt.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:43:51.216324+00:00
-- url     : https://prove2.me/theorems/ab1c923e-dbae-42a8-a418-a7521eb33d2a
-- title:
--   Theorem 2 — on directed instances, $\mathrm{Adaptive}_k \le O_{n\to\infty}\!\left(\frac{\log n}{\log\log n}\right)\mathrm{Static}_k$
-- statement:
--   Let $(V, \mathbf p)$ be a directed instance of influence maximization with $n = |V|$ vertices: $\mathbf p \in [0,1]^{V^2}$ is arbitrary (no symmetry $p_{u,v} = p_{v,u}$ is assumed), and every arc $a \in V^2$ is live independently with probability $p_a$. Then
--   $$
--   \mathrm{Adaptive}_k(V, \mathbf p) \;\le\; O_{n\to\infty}\!\left(\frac{\log n}{\log\log n}\right)\mathrm{Static}_k(V, \mathbf p).
--   $$
--   Explicitly: there are absolute constants $C$ and $N$ such that every instance with $n \ge N$ vertices and every budget $k \in \mathbb N$ satisfy
--   $$
--   \mathrm{Adaptive}_k(V, \mathbf p) \;\le\; C\,\frac{\log n}{\log\log n}\,\mathrm{Static}_k(V, \mathbf p).
--   $$
--   Here $\mathrm{Adaptive}_k$ is the optimum over all adaptive policies with budget $k$, full-adoption feedback and external randomness, and $\mathrm{Static}_k$ is the optimum of $\mathbb E[\sigma(S)]$ over seed sets $|S| \le k$.
--
--   This is the first sublogarithmic bound on the adaptivity gap of general directed instances, improving the earlier $\lceil n^{1/3} \rceil$.
--
--   **Formalization Note** $C$ and $N$ are quantified before the vertex type, the probabilities and the budget, so they depend on nothing. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: p ∈ [0,1]^{V²} as part of an instance → hypothesis ∀ u v, 0 ≤ p u v ∧ p u v ≤ 1 on p : V → V → ℝ, loops (v, v) included as in V²; reason: same instances
--   - encoding: Adaptive_k = max over π ∈ Π_k → the published InflMaxAdapt.Adaptive: sSup of the values of all policies with measurable decision rules on probability spaces (Ω : Type, μ); reason: the value set is bounded by |V|; a bound on the sSup is a bound on every policy value, as in the published Theorem 1
--   - encoding: Adaptive_k ≤ O_{n→∞}(log n / log log n) Static_k for every directed instance with n vertices → ∃ C : ℝ, ∃ N : ℕ, for every V with N ≤ |V|, every p ∈ [0,1]^{V²} and every k : ℕ, Adaptive p k ≤ C · (log n / log log n) · Static p k, with n = |V|; reason: the meaning of O_{n→∞} with the constant uniform in the instance and in k, as the proof (explicit bound depending on n only, printed p.11) gives
--   - encoding: log (base unspecified) → Real.log (natural logarithm); reason: another base changes only the constant C
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Theorem 2, printed p.3 (PDF p.4); proof in Section 3, printed pp.9–11 (PDF pp.10–12)

import Mathlib
import Definitions.Def_InflMaxAdapt_Static
import Definitions.Def_InflMaxAdapt_Adaptive

open MeasureTheory

namespace InflMaxAdapt.Supplement

open InflMaxAdapt

/-- Theorem 2 (directed graphs; printed p.3 = PDF p.4, proof in Section 3, printed pp.9–11 = PDF
pp.10–12, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and
Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): for every directed instance
of influence maximization with `n` vertices,
`Adaptive_k ≤ O_{n→∞}(log n / log log n) · Static_k`.

The `O_{n→∞}` is uniform in the instance and the budget: there are constants `C` and `N` such that
every instance `(V, p)` with `n = |V| ≥ N` vertices (arbitrary `p ∈ [0,1]^{V²}`, no symmetry) and
every budget `k ∈ ℕ` satisfy `Adaptive_k ≤ C · (log n / log log n) · Static_k`.

**Formalization Note** `C` and `N` are quantified before the vertex type, `p` and `k`, so they are
absolute. `log` is the natural logarithm; another base changes only `C`. -/
theorem theorem_2 :
    ∃ C : ℝ, ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → V → ℝ), (∀ u v, 0 ≤ p u v ∧ p u v ≤ 1) → ∀ k : ℕ,
        Adaptive p k ≤
          C * (Real.log (Fintype.card V) / Real.log (Real.log (Fintype.card V))) * Static p k := by sorry

end InflMaxAdapt.Supplement
