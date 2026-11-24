-- Prove2me | Theorems.Thm_GreedyRS_Greedy_Supplement_theorem5_enhanced
-- name    : GreedyRS.Greedy.Supplement.theorem5_enhanced
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:30:50.206925+00:00
-- url     : https://prove2.me/theorems/8d0b2d0d-0d7b-49d2-b040-ac82f17c0231
-- title:
--   Theorem 5 — EFG+ calibrated sample-optimality lower bound
-- statement:
--   Consider mutually independent observations $X_{ij}\sim N(\mu_i,\sigma_i^2)$ with $\sigma_i^2>0$, a uniform gap $\mu_i\le\mu_1-\gamma$ for $i\ge2$, and $\sigma_i^2\le\bar\sigma^2$ for all $i$, where $\gamma,\bar\sigma>0$. Let $G\ge2$ be an integer, let $n_0\ge G$ be real, let $n_{\rm sd}\ge1$ be an integer, and let $n_g\in\mathbb R$. Set
--   $$n^r=\left\lfloor\frac{n_0(2^G-1)}{G2^{r-1}}\right\rfloor,\qquad r=1,\ldots,G.$$
--   Let $C(x;n)$ be the expected strict crossing time from $n$ of an independent standard-normal running average. Suppose
--   $$n_0+n_g>C(\gamma/\bar\sigma;n^1).$$
--   Run the enhanced explore-first greedy procedure (Procedure 3): seed each alternative using $n_{\rm sd}$ observations; rank decreasingly by seed average; allocate fresh exploration counts $n^r$ according to its exact groups; then sample the current leader until the total budget $B_k=\lfloor(n_{\rm sd}+n_0+n_g)k\rfloor$ is exhausted, and select the final leader. All post-seeding averages exclude seed observations. Write $\bar X_1^{\rm fresh}(n)$ for the best alternative's average of the first $n$ post-seeding observations.
--
--   There exists $\gamma_0\in(0,\gamma)$ satisfying
--   $$C((\gamma-\gamma_0)/\bar\sigma;n^1)=n_0+n_g,$$
--   and for every such solution the unconditional probability of correct selection satisfies
--   $$\liminf_{k\to\infty}\mathrm{PCS}_k^{+}\ge P\{\min_{n\ge n^G}\bar X_1^{\rm fresh}(n)>\mu_1-\gamma_0\}.$$
--
--   This establishes the EFG+ sample-optimality bound without a successful-seeding assumption. The calibration uses the largest exploration level $n^1$, while the survival event starts at the smallest level $n^G$.
--
--   **Formalization Note** The finite groups use the precise rank intervals and floors of Procedure 3. The algorithm uses the actual sum of allocated exploration observations, so unused exploration budget goes to the greedy loop. The total budget includes seeding once. The fresh tail has the source's normal running-average law, independently of the seed ordering. No claim of asymptotic tightness is made for EFG+.
--
--   Differences from the source:
--   - reading: normal observations with standard-deviation normalizations → strictly positive variance for every row; reason: the shared nondegenerate-normal reading excludes zero-variance rows where the source normalizations divide by zero
--   - reading: real linear sampling budget B=ck → integer budget floor(ck); reason: an observation count is integral; rounding changes the budget by less than one and not its limiting coefficient
--   - encoding: alternatives 1 through k, considered as k grows → alternatives 0 through k-1 from one infinite observation array; reason: index 0 is the best; coupling preserves every finite-k observation law and PCS
--   - reading: unspecified tie handling in argmax → the smallest alternative index wins ties; reason: the published convention is deterministic and ties have probability zero under independent positive-variance normals
--   - encoding: a minimum of normal running averages and its survival probability → AboveFrom requires a bounded-below tail and a strict infimum inequality; probabilities and limits are in the extended nonnegative reals; reason: the tail minimum is attained almost surely; these types prevent junk infima and preserve infinite crossing-time expectations
--   - encoding: gamma_0 is described as a constant satisfying an exact C equation → existence in (0,gamma), followed by the conclusion for every solution; reason: the conclusion includes the existence implicit in the source instead of a potentially vacuous implication
--   - encoding: n_g > C(x;n)-n_0 → C(x;n) < ofReal(n_0+n_g); reason: the additive inequality is equivalent on the positive finite domain and avoids truncated extended subtraction
--   - encoding: Procedure 3 requires k >= 2^G-1 → the selection map returns 0 below that threshold and uses exact Procedure 3 above it; reason: G is fixed, so only finitely many k are outside the source procedure domain and no asymptotic instance is excluded
--   - encoding: seeding observations are discarded before exploration and greedy sampling → the first n_sd entries of each row determine the rank and freshTail shifts all later averages by n_sd; reason: the mutually independent infinite array supplies the exact independent fresh law required on p. 27
--   - generalization: n_0 >= G is the exploration budget per alternative in Theorem 5 → n_0 is real, with only each n^r floored to a natural number; reason: the source's n_0 is an integer exploration size; every real n_0 >= G is allowed, integer n_0 recovers the source exactly, and the floors n^r and the budget floor make the procedure well defined for real n_0
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 26, Theorem 5; Assumption 1, p. 12; Procedure 3, p. ec10 (PDF 49); EC.2.5, pp. ec10–ec11 (PDF 49–50); discarded seeding observations, p. 27

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Supplement_Enhanced

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

namespace GreedyRS.Greedy.Supplement

/-- Theorem 5: the calibrated EFG+ lower bound, with n¹ in C and n^G in the survival event. -/
theorem theorem5_enhanced {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : NormalArray P μ v X) (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (G : ℕ) (hG : 2 ≤ G) (n0 : ℝ) (hn0 : (G : ℝ) ≤ n0)
    (nsd : ℕ) (hnsd : 1 ≤ nsd) (ng : ℝ)
    (hng : Cn0 (γ / σbar) (groupLevel n0 G 1) < ENNReal.ofReal (n0 + ng)) :
    (∃ γ0 ∈ Set.Ioo 0 γ,
      Cn0 ((γ - γ0) / σbar) (groupLevel n0 G 1) = ENNReal.ofReal (n0 + ng)) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ,
      Cn0 ((γ - γ0) / σbar) (groupLevel n0 G 1) = ENNReal.ofReal (n0 + ng) →
      P {ω | AboveFrom (runMean (freshTail nsd (fun i j => X i j ω)) 0)
        (groupLevel n0 G G) (μ 0 - γ0)} ≤
      Filter.liminf (fun k : ℕ => plusPCS P X k nsd G n0
        ⌊((nsd : ℝ) + n0 + ng) * k⌋₊) Filter.atTop := by sorry

end GreedyRS.Greedy.Supplement
