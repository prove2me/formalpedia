-- Prove2me | Theorems.Thm_MaxEntOCRS_theorem_1
-- name    : MaxEntOCRS.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:18.817124+00:00
-- url     : https://prove2.me/theorems/8a2fbd77-7b47-4486-a6a4-9dde14176666
-- title:
--   Theorem 1 — the maximum-entropy stationary OCRS is $\alpha$-selectable on every graph, and $\alpha = (\sqrt3-1)/2$ is best
-- statement:
--   Let $\alpha = (\sqrt3 - 1)/2$. For every finite loopless multigraph $G = (V, E)$ and every $x$ in the fractional matching polytope
--   $$
--   P(G) = \Big\{ x \ge 0 : \sum_{e \ni v} x_e \le 1 \text{ for all } v \Big\}:
--   $$
--
--   1. **(selectability of the template)** the maximum-entropy distribution $\mu^*$ on $\mathcal M(G)$ with marginals $\alpha x$ exists, and it satisfies $\Pr_{\mu^*}[\mathrm{Add}(e)] \ge \alpha$ for every edge $e$;
--   2. **(the OCRS)** consequently the maximum-entropy simulate-then-replace scheme of Aminian, Niazadeh and Nuti is an $\alpha$-selectable stationary OCRS: its acceptance probabilities $\theta_e/x_e$ lie in $[0, 1]$, and for every arrival order of the edges the output has law $\mu^*$ and contains each edge $e$ with probability at least $\alpha x_e$;
--   3. **(tightness)** $\alpha$ is the best constant for this template: for every $\tau \in (\alpha, 1]$ there is a finite loopless multigraph, a point $x \in P(G)$ and an edge $e$ such that the maximum-entropy distribution with marginals $\tau x$ exists and every such distribution has $\Pr[\mathrm{Add}(e)] < \tau$.
--
--   This settles the conjecture of Aminian, Niazadeh and Nuti that the maximum-entropy template achieves $\alpha$ on general graphs.
--
--   **Formalization Note** Distributions on matchings are weight functions on edge sets; the scheme is a law transform with one activation coin per arrival; an arrival order is a list of all edges without repetition; the tightness instance is stated on vertex type $\mathrm{Fin}\,n$ and edge type $\mathrm{Fin}\,m$.
--
--   Differences from the source:
--   - reading: the maximum-entropy distribution with marginals αx satisfies Pr[Add(e)] ≥ α → a maximizer exists, and every maximizer satisfies the bound; reason: the definite article asserts existence; the maximizer is unique
--   - reading: the scheme is an α-selectable stationary OCRS → for every arrival order listing each edge once: acceptance probabilities in [0, 1] for edges with x_e > 0, output law equal to µ*, and selection probability ≥ α x_e; reason: the scheme of p.4 run against a fixed order; the adaptive-adversary remark of p.3 is outside the theorem's statement
--   - encoding: the simulate-then-replace scheme with acceptance probability θ_e/x_e → the law transform schemeLaw with one Bernoulli(x_e) activation per arrival; acceptance written Pr(e ∈ M)/(x_e Pr[Add(e)]); reason: activations are independent and revealed at arrival; equals θ_e/x_e for the Gibbs measure
--   - reading: α is the best constant for this template → for every τ > α some instance has a maximum-entropy distribution with marginals τx, and every such distribution has Pr[Add(e)] < τ for some edge e; reason: no larger constant makes the template τ-selectable on every instance (pp.8–9)
--   - generalization: τ ∈ (α, 1) for the template's α′ ∈ (0, 1) → τ ∈ (α, 1]; reason: the paper also treats τ = 1 (p.9); the statement for τ < 1 is included
--   - encoding: distributions on M(G) → weight functions on Finset E, nonnegative, vanishing off matchings, summing to 1; reason: Lean convention; same distributions
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Theorem 1, p.2 (scheme: Section 2, p.4; proof p.5; tightness: Section 6, pp.8–9)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_OnlineCRS_Matching_Model
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_IsMaxEntropy
import Definitions.Def_MaxEntOCRS_addProb
import Definitions.Def_MaxEntOCRS_acceptProb
import Definitions.Def_MaxEntOCRS_schemeLaw
import Definitions.Def_MaxEntOCRS_edgeMarginal

namespace MaxEntOCRS

/-- Theorem 1 (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.2). For every finite loopless multigraph `G` and every `x` in the
fractional matching polytope `P(G) = {x ≥ 0 : ∑_{e ∋ v} x_e ≤ 1 for all v}`:

(a) the maximum-entropy distribution with marginals `αx` exists, and it satisfies
`Pr[Add(e)] ≥ α` for every edge `e`;

(b) consequently the maximum-entropy simulate-then-replace scheme (§2, p.4) is an
`α`-selectable stationary OCRS: its acceptance probabilities lie in `[0, 1]`, and for every
arrival order the output has law `µ*` and selects every edge `e` with probability at least
`α x_e`;

(c) `α = (√3 − 1)/2` is the best constant for this template: for every `τ ∈ (α, 1]` there is an
instance on which the maximum-entropy distribution with marginals `τx` exists and every such
distribution has `Pr[Add(e)] < τ` for some edge `e` (§6, "Tightness", pp.8–9).

**Formalization Note** Distributions on matchings are weight functions on `Finset E`
(`IsMatchingDist`); the scheme is the law transform `schemeLaw` with one Bernoulli(`x_e`)
activation per arrival; an arrival order is a list of the edges without repetition. -/
theorem theorem_1 :
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ), x ∈ OnlineCRS.Matching.matchingRelax G →
        (∃ μ, IsMaxEntropy G (alpha • x) μ) ∧
          ∀ μ, IsMaxEntropy G (alpha • x) μ → ∀ e, alpha ≤ addProb G μ e) ∧
      (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ), x ∈ OnlineCRS.Matching.matchingRelax G →
        ∀ μ, IsMaxEntropy G (alpha • x) μ →
          ∀ σ : List E, σ.Nodup → (∀ e, e ∈ σ) →
            (∀ e, 0 < x e → 0 ≤ acceptProb G x μ e ∧ acceptProb G x μ e ≤ 1) ∧
              schemeLaw G x μ σ = μ ∧ ∀ e, alpha * x e ≤ edgeMarginal (schemeLaw G x μ σ) e) ∧
      ∀ τ : ℝ, alpha < τ → τ ≤ 1 →
        ∃ (n m : ℕ) (G : EdmondsMatching65.Polyhedron.Graph (Fin n) (Fin m)) (x : Fin m → ℝ) (e : Fin m),
          x ∈ OnlineCRS.Matching.matchingRelax G ∧ (∃ μ, IsMaxEntropy G (τ • x) μ) ∧
            ∀ μ, IsMaxEntropy G (τ • x) μ → addProb G μ e < τ := by sorry

end MaxEntOCRS
