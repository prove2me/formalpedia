-- Prove2me | Theorems.Thm_GreedyRS_Greedy_Supplement_theorem3_full
-- name    : GreedyRS.Greedy.Supplement.theorem3_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:30:18.826234+00:00
-- url     : https://prove2.me/theorems/d172806d-b5de-4438-b1db-59e32613966a
-- title:
--   Theorem 3 — EFG sample optimality and SC-CV tightness (corrected: common-σ calibration)
-- statement:
--   Consider mutually independent normal observations $X_{ij}\sim N(\mu_i,\sigma_i^2)$ with positive variances. Alternative 1 is the best. Assume $\gamma>0$, $\bar\sigma>0$, $\mu_i\le\mu_1-\gamma$ for every $i\ge2$, and $\sigma_i^2\le\bar\sigma^2$ for every $i$, uniformly as the number $k$ of alternatives grows. Write $\bar X_i(n)$ for the average of the first $n$ observations, and let $C(x;n)=\mathrm E[\inf\{m\ge n:\bar Z(m)<x\}]$ for independent standard normals $Z_j$, with an infinite value for a never-crossing path.
--
--   Let $n_0\ge1$ be any integer, $n_g\in\mathbb R$, $c=n_0+n_g$, and suppose $c>C(\gamma/\bar\sigma;n_0)$. EFG takes $n_0$ observations per alternative, then samples the current largest running average until its total budget $B_k=\lfloor ck\rfloor$ is exhausted, and selects the final leader. There exists $\gamma_{0,\bar\sigma}\in(0,\gamma)$ satisfying
--   $$C((\gamma-\gamma_{0,\bar\sigma})/\bar\sigma;n_0)=c.$$
--   For every such solution,
--   $$\liminf_{k\to\infty}\mathrm{PCS}_k\ge P\{\min_{n\ge n_0}\bar X_1(n)>\mu_1-\gamma_{0,\bar\sigma}\}.$$
--   Furthermore, if all inferior means equal $\mu_1-\gamma$ and all variances equal $\sigma^2>0$, there exists $\gamma_{0,\sigma}\in(0,\gamma)$ satisfying $C((\gamma-\gamma_{0,\sigma})/\sigma;n_0)=c$, and for every such solution
--   $$\lim_{k\to\infty}\mathrm{PCS}_k=P\{\min_{n\ge n_0}\bar X_1(n)>\mu_1-\gamma_{0,\sigma}\}.$$
--
--   This includes both the general sample-optimality lower bound and its exact limiting value under the slippage configuration with common variance (SC-CV), for every positive exploration size. The previously proved first clause is imported as a dependency; the entire conjunction, including tightness, is the new target.
--
--   **Formalization Note** The two calibrated constants may differ when $\bar\sigma>\sigma$. Equality is calibrated at the actual common $\sigma$, as the Theorem 2 analogy on p. 23 and proof EC.2.2 specify. The strict budget assumption at $\bar\sigma$ implies admissibility at $\sigma$. No special exploration size is imposed.
--
--   Differences from the source:
--   - reading: normal observations with standard-deviation normalizations → strictly positive variance for every row; reason: the shared nondegenerate-normal reading excludes zero-variance rows where the source normalizations divide by zero
--   - reading: real linear sampling budget B=ck → integer budget floor(ck); reason: an observation count is integral; rounding changes the budget by less than one and not its limiting coefficient
--   - encoding: alternatives 1 through k, considered as k grows → alternatives 0 through k-1 from one infinite observation array; reason: index 0 is the best; coupling preserves every finite-k observation law and PCS
--   - reading: unspecified tie handling in argmax → the smallest alternative index wins ties; reason: the published convention is deterministic and ties have probability zero under independent positive-variance normals
--   - encoding: a minimum of normal running averages and its survival probability → AboveFrom requires a bounded-below tail and a strict infimum inequality; probabilities and limits are in the extended nonnegative reals; reason: the tail minimum is attained almost surely; these types prevent junk infima and preserve infinite crossing-time expectations
--   - encoding: gamma_0 is described as a constant satisfying an exact C equation → existence in (0,gamma), followed by the conclusion for every solution; reason: the conclusion includes the existence implicit in the source instead of a potentially vacuous implication
--   - encoding: n_g > C(x;n)-n_0 → C(x;n) < ofReal(n_0+n_g); reason: the additive inequality is equivalent on the positive finite domain and avoids truncated extended subtraction
--   - correction: the SC-CV equality appears to inherit calibration at an arbitrary variance bound sigma_bar → the general lower bound uses sigma_bar, while SC-CV equality has its own calibration at the actual common sigma; reason: p. 23 explicitly generalizes Theorem 2 and EC.2.2 repeats its proof; with gamma=1, sigma=1, sigma_bar=2, n_0=1 and c=C(1/4), the inherited gamma_0=1/2 predicts 1/C(1/2), whereas Theorem 2 gives 1/C(3/4); see DISPROOF.md
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 23, Theorem 3; Assumption 1, p. 12; Procedure 2, p. 21; EC.2.2, pp. ec6–ec7 (PDF 45–46); calibration correction supported by Theorem 2, p. 16

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
import Theorems.Thm_GreedyRS_EFG_theorem3_efg_sample_optimality

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

namespace GreedyRS.Greedy.Supplement

/-- Theorem 3 in full: the general lower bound and SC-CV convergence.
The first conjunct is exactly the published lower-bound clause, available from the imported theorem.
The SC-CV calibration uses the actual common σ, as in Theorem 2 and EC.2.2. -/
theorem theorem3_full {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : NormalArray P μ v X) (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (n0 : ℕ) (hn0 : 1 ≤ n0) (ng : ℝ)
    (hng : Cn0 (γ / σbar) n0 < ENNReal.ofReal ((n0 : ℝ) + ng)) :
    ((∃ γ0 ∈ Set.Ioo 0 γ, Cn0 ((γ - γ0) / σbar) n0 = ENNReal.ofReal ((n0 : ℝ) + ng)) ∧
      ∀ γ0 ∈ Set.Ioo 0 γ, Cn0 ((γ - γ0) / σbar) n0 = ENNReal.ofReal ((n0 : ℝ) + ng) →
        P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)} ≤
          Filter.liminf (fun k : ℕ => pcs P X k n0 ⌊((n0 : ℝ) + ng) * k⌋₊) Filter.atTop) ∧
    (∀ (σ : ℝ), 0 < σ → (∀ i, 1 ≤ i → μ i = μ 0 - γ) →
      (∀ i, (v i : ℝ) = σ ^ 2) →
      (∃ γ0 ∈ Set.Ioo 0 γ, Cn0 ((γ - γ0) / σ) n0 = ENNReal.ofReal ((n0 : ℝ) + ng)) ∧
      ∀ γ0 ∈ Set.Ioo 0 γ, Cn0 ((γ - γ0) / σ) n0 = ENNReal.ofReal ((n0 : ℝ) + ng) →
        Tendsto (fun k : ℕ => pcs P X k n0 ⌊((n0 : ℝ) + ng) * k⌋₊) atTop
          (𝓝 (P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)}))) := by sorry

end GreedyRS.Greedy.Supplement
