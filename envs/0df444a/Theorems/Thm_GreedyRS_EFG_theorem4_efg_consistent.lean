-- Prove2me | Theorems.Thm_GreedyRS_EFG_theorem4_efg_consistent
-- name    : GreedyRS.EFG.theorem4_efg_consistent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:42.461532+00:00
-- url     : https://prove2.me/theorems/35e225ff-f8e6-4271-90c8-9c5e7923f613
-- title:
--   Theorem 4, p. 24 — the explore-first greedy procedure is consistent: liminf_k PCS ≥ α with B = ⌊(n₀ + n_g)k⌋
-- statement:
--   Consider $k$ alternatives with independent normal observations $X_{ij}\sim N(\mu_i,\sigma_i^2)$, $\sigma_i^2>0$, alternative 1 the best, and suppose **Assumption 1** holds: there are constants $\gamma>0$ and $\bar\sigma^2>0$ with $\mu_1-\max_{i\ge2}\mu_i\ge\gamma$ and $\max_i\sigma_i^2\le\bar\sigma^2$, regardless of $k$. Let $C(x;n_0)=\mathrm E[\tilde N(x;n_0)]$, where $\tilde N(x;n_0)=\inf\{n\ge n_0:\bar Z(n)<x\}$ is the first time from $n_0$ on that the running average of iid standard normals drops below $x$.
--
--   Fix a PCS level $\alpha\in(0,1)$ and $\gamma_0\in(0,\gamma)$. Let the exploration size $n_0 \ge 1$ satisfy (5.3),
--   $$\Pr\Big\{\min_{n\ge n_0}\bar X_1(n)>\mu_1-\gamma_0\Big\}\ge\alpha,$$
--   and let
--   $$n_g \ \ge\ C\Big(\frac{\gamma-\gamma_0}{\bar\sigma};n_0\Big)-n_0 .$$
--   If the total sampling budget satisfies $B/k = n_0 + n_g$, the PCS of the explore-first greedy procedure satisfies
--   $$\liminf_{k\to\infty}\mathrm{PCS}\ \ge\ \alpha .$$
--
--   This is the consistency of the EFG procedure in the sense of Definition 2: every PCS level is reachable with a budget linear in the number of alternatives, which the plain greedy procedure cannot achieve.
--
--   **Formalization Note** The budget $B=(n_0+n_g)k$ is read as $\lfloor(n_0+n_g)k\rfloor$. The condition on $n_g$ is written additively in $[0,\infty]$: $C((\gamma-\gamma_0)/\bar\sigma;n_0)\le n_0+n_g$. Probabilities, the liminf and $C$ live in $[0,\infty]$. "$\min_{n\ge n_0}\bar X_1(n)>a$" means the path is bounded below from $n_0$ on and its infimum exceeds $a$. Positive variances are assumed. Alternatives are indexed from $0$ (Lean's $0$ is the paper's alternative 1); one observation array serves all $k$, and ties in every arg max go to the smallest index (a null event).
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 24, Theorem 4; Assumption 1, p. 12; Definition 2, p. 21

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem theorem4_efg_consistent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : GreedyRS.Greedy.NormalArray P μ v X) (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (γ0 : ℝ) (hγ0 : γ0 ∈ Set.Ioo 0 γ) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (h53 : ENNReal.ofReal α ≤
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)})
    (ng : ℝ) (hng : GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 ≤ ENNReal.ofReal (n0 + ng)) :
    ENNReal.ofReal α ≤
      Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k n0 ⌊((n0 : ℝ) + ng) * k⌋₊) Filter.atTop := by sorry

end GreedyRS.EFG
