-- Prove2me | Theorems.Thm_NonstatNV_theorem_2
-- name    : NonstatNV.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:34.998743+00:00
-- url     : https://prove2.me/theorems/9b0bda62-7af4-4f46-92d4-49b423da4797
-- title:
--   Theorem 2 (corrected: constant depends on γ, T ≥ 2) — PERP has regret $O(\sqrt{\log T}\,T^{\min\{(3+v)/4,a\}})$ without knowing $a$
-- statement:
--   Consider a Nonstationary Newsvendor model with predictions satisfying the standing assumptions (Assumption 1) and Assumption 2 with constant $\ell$, and let $\delta>0$ bound the demand noise uniformly: $\mathbb E[\exp((d-\mu)^2/\delta^2)]\le2$ for $d\sim D_\mu$, every $\mu\in[\mu_{\min},\mu_{\max}]$. Let $\kappa>0$ and $\gamma>0$ be the scaling constants of the Prediction-Error-Robust Policy (PERP), with
--
--   $$
--   \kappa\gamma^2\ge 288e\,\delta^2
--   $$
--
--   (condition (G.1) with $\rho=1/(144e)$). Then there is a constant $C$ such that for every horizon $T\ge2$, every variation parameter $v\in[0,1]$, every accuracy parameter $\alpha\in[0,1]$, every measurable argmin selection, and every instance $(\mu_t,b_t,h_t)$ with demand variation $V_\mu\le T^v$ and predictions with $\sum_{t=1}^T|a_t-\mu_t|\le T^{\alpha}$, the regret of PERP satisfies
--
--   $$
--   \mathbb E\Big[\sum_{t=1}^{T}\big(C_t(\mu_t,q_t)-C_t(\mu_t,q_t^*)\big)\Big]\le C\sqrt{\log T}\;T^{\min\{(3+v)/4,\ \alpha\}} .
--   $$
--
--   Without knowing the prediction accuracy, PERP matches up to $\sqrt{\log T}$ the regret $\Theta(T^{\min\{(3+v)/4,a\}})$ that is optimal when $a$ is known (Proposition 2). This is the paper's main result.
--
--   Differences from the source:
--   - correction: R(T) ≤ min{3C_{Lemma 2} √(log T) T^{(3+v)/4}, 2ℓT^a} with C_{Lemma 2} independent of γ → R(T) ≤ C √(log T) T^{min{(3+v)/4, α}} with C depending on the model, ℓ, δ, κ and γ; reason: the printed bound is false: with D_μ the point mass at μ ∈ [0, 1], Q = {0, 1}, b = h = 1 (ℓ = 1), κ = 1, v = 0, μ_t = 0, a_t = 1 (error T = T¹), γ = 200 and T = 10¹², the test never fires, PERP orders 1 in every period and its regret is 10¹², while the printed bound is at most min{3·8.82·√(log 10¹²)·10⁹, 2·10¹²} < 1.41·10¹¹; the proof (pp.48–51) concludes R ≤ C T^{min{(3+v)/4,a}} √(log T) with C built from constants that contain γ. The second branch 2ℓT^a cannot be kept either, for any first-branch constant: with D_μ = Bernoulli(μ), μ ∈ [0, 1] (ℓ = 1, noise δ = 1/√(ln 2)), Q = {0, 1}, b = h = 1, κ = 1, γ = 34, v = 0, μ_t = 1/6, a_1 = a_2 = a_3 = 1/2 and a_t = 1/6 for t ≥ 4 (error 1 = T⁰, so a = 0), a selection taking q = 1 at the tie μ̂ = 1/2, and T = 10¹², the first three periods cost exactly 3·(2/3) = 2 = 2ℓT^a, and on the positive-probability path with every demand equal to 1 the test fires ((T − n)·5/6 > (34√(log T) + 2)T^{3/4}) and PERP then orders 1 at regret 2/3 per period, so the regret is > 2ℓT^a
--   - correction: every T → T ≥ 2; reason: at T = 1 the factor √(log T) is 0, so the bound is 0, while the instance above with T = 1 has regret 1; no constant repairs T = 1
--   - reading: δ = sup_μ ‖D_μ‖ (Lemma 2) and δ = max_s δ_s (G.1) → a δ > 0 with E[exp((d − μ)²/δ²)] ≤ 2 for every μ ∈ [μmin, μmax]; reason: γ is an input fixed before the instance, so (G.1) can only be met if the noise bound is uniform over the family; every admissible δ is allowed
--   - reading: γ sufficiently large: ρκγ²/δ² ≥ 2 (G.1) with a universal ρ, 1/ρ ≤ 144e (Lemma 3) → every γ > 0 with κγ² ≥ 288e·δ²; reason: (G.1) with ρ = 1/(144e), the value Lemma 3 licenses
--   - reading: break in Algorithm 4 → PERP plays the Fixed-Time-Window Policy from the first firing period on; reason: the proof states 'after time s we have π^PERP = π^fixed' (p.50)
--   - reading: ℓ may depend on (b, h, q) in Assumption 2 → one ℓ for all b ∈ [0, bmax], h ∈ [0, hmax], q ∈ Q; reason: the paper asserts a single ℓ and uses it in every bound
--   - encoding: q_t ∈ argmin_{q∈Q} C_t(μ̂_t, q) → q_t = sel(μ̂_t, b_t, h_t) for every measurable argmin selection sel, chosen after C; reason: ties are broken arbitrarily; measurability only makes the expectation defined
--   - encoding: worst-case regret R(T) = sup over D(v), costs and predictions with accuracy parameter a → a bound for every instance in the class and every α ∈ [0, 1] with prediction error ≤ T^α; reason: a bound for every instance is equivalent to a bound on the supremum; the bound increases with α for T ≥ 2, so 'smallest a' and 'any α' are equivalent
--   - encoding: periods t = 1, …, T; n = ⌈κT^{(1−v)/2}⌉ (the proof ignores the rounding); log → demand paths indexed by ℕ with periods 1, …, T; the ceiling kept; Real.log; reason: Lean conventions; log is the natural logarithm, which (G.1)'s step exp(−(ρκγ²/δ²) log T) ≤ T^{−2} requires
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Theorem 2, p.23 (proof Appendix G, pp.48–51)

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_LipschitzCost
import Definitions.Def_NonstatNV_Model_NoiseMGFBound
import Definitions.Def_NonstatNV_Model_IsArgminSelection
import Definitions.Def_NonstatNV_Model_IsInstance
import Definitions.Def_NonstatNV_demandVariation
import Definitions.Def_NonstatNV_Model_intervalRegret
import Definitions.Def_NonstatNV_Model_perpPolicy

open MeasureTheory

namespace NonstatNV

/-- **Theorem 2 (Upper Bound: Known v and Unknown a)** (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.23; proof Appendix G, pp.48–51),
corrected. Fix the model (Assumptions 1 and 2), a uniform sub-Gaussian bound `δ > 0` on the demand
noise, and the inputs `κ > 0` and `γ > 0` of PERP with `κγ² ≥ 288e·δ²` ((G.1) with `ρ = 1/(144e)`).
There is a constant `C` such that for every horizon `T ≥ 2`, every `v ∈ [0, 1]`, every `α ∈ [0, 1]`,
every measurable argmin selection and every instance in `𝒟(v)` whose predictions have total error
`Σ_{t=1}^T |a_t − μ_t| ≤ T^α`, the regret of PERP is at most `C √(log T) T^{min{(3+v)/4, α}}`.

**Formalization Note** The printed bound `min{3C_{Lemma 2} √(log T) T^{(3+v)/4}, 2ℓT^a}` is false
(its constant does not depend on `γ`, it is `0` at `T = 1`, and its branch `2ℓT^a` without an
additive constant fails when PERP switches on a rare demand path); this is the conclusion of the
paper's proof, with `C` depending on the model, `ℓ`, `δ`, `κ` and `γ` only. `C` is chosen before
`T`, `v`, `α`, the selection and the instance. `Real.log` is the natural logarithm. -/
theorem theorem_2 (M : Model) (ℓ δ : ℝ) (hM : M.Standing) (hℓ : M.LipschitzCost ℓ)
    (hδ : 0 < δ) (hnoise : M.NoiseMGFBound δ) (κ γ : ℝ) (hκ : 0 < κ) (hγ : 0 < γ)
    (hG1 : 288 * Real.exp 1 * δ ^ 2 ≤ κ * γ ^ 2) :
    ∃ C : ℝ, ∀ T : ℕ, 2 ≤ T → ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ∀ sel : ℝ → ℝ → ℝ → ℝ, M.IsArgminSelection sel →
      ∀ μ b h a : ℕ → ℝ, M.IsInstance T μ b h → demandVariation μ T ≤ (T : ℝ) ^ v →
        ∑ t ∈ Finset.Icc 1 T, |a t - μ t| ≤ (T : ℝ) ^ α →
          M.intervalRegret μ b h (M.perpPolicy sel b h a T v κ γ) 1 T ≤
            C * Real.sqrt (Real.log T) * (T : ℝ) ^ min ((3 + v) / 4) α := by sorry

end NonstatNV
