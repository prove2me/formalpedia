-- Prove2me | Theorems.Thm_GreedyRS_EFG_theorem3_efg_sample_optimality
-- name    : GreedyRS.EFG.theorem3_efg_sample_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:38.074373+00:00
-- url     : https://prove2.me/theorems/90bd3c22-6237-45db-80c0-f48331e69811
-- title:
--   Theorem 3, p. 23 — if n_g > C(γ/σ̄; n₀) − n₀ and B = ⌊(n₀ + n_g)k⌋, then liminf PCS ≥ Pr{min_{n≥n₀} X̄₁(n) > μ₁ − γ₀}
-- statement:
--   Consider $k$ alternatives with independent normal observations $X_{ij} \sim N(\mu_i, \sigma_i^2)$, $\sigma_i^2 > 0$, and suppose **Assumption 1** holds: there are constants $\gamma > 0$ and $\bar\sigma^2 > 0$ with $\mu_1 - \max_{i\ge2}\mu_i \ge \gamma$ and $\max_i \sigma_i^2 \le \bar\sigma^2$, regardless of $k$. Let $n_0 \ge 1$ and suppose the budget satisfies $B/k = n_0 + n_g$ with
--   $$n_g > C\Big(\frac{\gamma}{\bar\sigma}; n_0\Big) - n_0,$$
--   where $C(x;n_0) = \mathrm E[\tilde N(x;n_0)]$. Then there is $\gamma_0 \in (0,\gamma)$ with $C\big(\frac{\gamma-\gamma_0}{\bar\sigma}; n_0\big) = n_g + n_0$, and for such $\gamma_0$ the PCS of the EFG procedure satisfies
--   $$\liminf_{k\to\infty} \mathrm{PCS} \ \ge\ \Pr\Big\{\min_{n\ge n_0}\bar X_1(n) > \mu_1 - \gamma_0\Big\}.$$
--
--   This is the sample optimality of the EFG procedure: a budget linear in $k$ keeps the PCS bounded below by a positive constant. It generalizes Theorem 1 from $n_0 = 1$ to every $n_0 \ge 1$.
--
--   **Formalization Note** The budget $B = (n_0+n_g)k$ is read as $\lfloor (n_0+n_g)k\rfloor$. Conditions involving $C(\cdot;n_0) - n_0$ are written additively in $[0,\infty]$ ($C(\gamma/\bar\sigma;n_0) < n_0 + n_g$). The existence of $\gamma_0$, implicit in the paper, is stated as a conclusion, so the bound cannot hold vacuously. "$\min_{n\ge n_0}\bar X_1(n) > a$" means the path is bounded below from $n_0$ on and its infimum exceeds $a$ (the minimum is attained a.s. by Lemma 3). Positive variances are assumed, as the paper's normalizations divide by $\sigma_i$. Only the first sentence of Theorem 3 is stated (the slippage-configuration limit is not). One observation array serves all $k$; problem $k$ reads its first $k$ rows, which changes no PCS.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 23, Theorem 3 (first sentence); Assumption 1, p. 12; proof EC.2.2, p. ec7

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem theorem3_efg_sample_optimality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : GreedyRS.Greedy.NormalArray P μ v X) (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (n0 : ℕ) (hn0 : 1 ≤ n0) (ng : ℝ)
    (hng : GreedyRS.Greedy.Cn0 (γ / σbar) n0 < ENNReal.ofReal (n0 + ng)) :
    (∃ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 = ENNReal.ofReal (n0 + ng)) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 = ENNReal.ofReal (n0 + ng) →
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)} ≤
        Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k n0 ⌊((n0 : ℝ) + ng) * k⌋₊) Filter.atTop := by sorry

end GreedyRS.EFG
