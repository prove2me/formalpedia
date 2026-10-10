-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_lemma_3
-- name    : LuoSunLiu.DIP.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:17.963278+00:00
-- url     : https://prove2.me/theorems/ec04e1ba-21fe-46a8-99a7-4b1b60929451
-- title:
--   Lemma 3, pp. 20–21 — M-LinUCB on a PLB has, w.p. ≥ 1 − δ, R^{PLB}_{T₀} ≤ 2√(2dT₀β̃_{T₀} log((dλ + T₀a²_max)/(dλ))) + 2a_max C_p T₀ + 2d
-- statement:
--   Consider a perturbed linear bandit in dimension $d \ge 1$ with perturbation constant $C_p$ that satisfies Conditions 1–4, with constants $C_1 \ge 0$ and $a_{\max} > 0$. Let $\lambda > 0$, $\delta \in (0, 1)$ and $T_0 \ge 1$, and suppose that on every sample path the actions $A_1, \dots, A_{T_0}$ are a run of M-LinUCB (Algorithm 5) with
--   $$\beta_t = \tilde\beta_t = 1 \vee \Bigl(C_1\sqrt{\lambda d} + \sqrt{2\log(1/\delta) + d\log\tfrac{d\lambda + (t-1)a_{\max}^2}{d\lambda}}\Bigr)^2 .$$
--   Then with probability at least $1 - \delta$,
--   $$R^{PLB}_{T_0} \le 2\sqrt{2dT_0\tilde\beta_{T_0}\log\frac{d\lambda + T_0a_{\max}^2}{d\lambda}} + 2a_{\max}C_pT_0 + 2d .$$
--
--   The bound is the classical $\tilde O(d\sqrt{T_0})$ linear-bandit rate plus a term linear in the perturbation; in the pricing application $C_p = 2L\|\hat\theta - \theta_0\|_1$ by Lemma 1.
--
--   **Formalization Note** "With probability at least $1-\delta$" is per $T_0$, as printed, in the inner-measure reading (a measurable event of probability at least $1 - \delta$ on which the bound holds). The action sets are finite, and nonempty because they contain the selected action; the paper's $\delta \in (0,1)$ from Lemmas S4–S5 is made explicit. The algorithm's tie-breaking is arbitrary. $\mathcal F$ is any filtration to which the actions are predictable and the noise adapted; the measurability of $\xi_t$ is not required.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, pp. 20–21, Lemma 3; proof pp. 41–44

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_PLB

open MeasureTheory ProbabilityTheory

namespace LuoSunLiu.DIP

/-- Lemma 3 (Luo, Sun and Liu, arXiv:2109.07340v2, pp. 20–21; proof pp. 41–44). Consider a
perturbed linear bandit with perturbation constant `C_p` satisfying Conditions 1–4 (Condition 4:
conditionally 1-sub-Gaussian noise). For `λ > 0`, `δ ∈ (0, 1)` and `T₀ ≥ 1`, if on every sample
path the actions up to `T₀` are a run of M-LinUCB (Algorithm 5) with
`β_t = β̃_t = 1 ∨ (C₁√(λd) + √(2 log(1/δ) + d log((dλ + (t-1)a²_max)/(dλ))))²`, then with
probability at least `1 - δ`,
`R^{PLB}_{T₀} ≤ 2√(2dT₀β̃_{T₀} log((dλ + T₀a²_max)/(dλ))) + 2a_max C_p T₀ + 2d`. -/
theorem lemma_3 {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (ξ : ℕ → Ω → Fin d → ℝ) (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) (A : ℕ → Ω → Fin d → ℝ)
    (Z η : ℕ → Ω → ℝ) (Cp C1 amax lam δ : ℝ)
    (hPLB : IsPLBModel P ℱ ξ 𝒜 A Z η 1) (hCp : HasPerturbation ξ Cp)
    (hCond1 : Condition1 ξ 𝒜) (hCond2 : Condition2 ξ C1) (hCond3 : Condition3 𝒜 amax)
    (hC1 : 0 ≤ C1) (hamax : 0 < amax) (hlam : 0 < lam) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (T0 : ℕ) (hT0 : 1 ≤ T0)
    (hrun : ∀ ω, IsMLinUCBRunAt lam (betaTilde C1 amax lam d δ) 𝒜 A Z T0 ω) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
      ∀ ω ∈ E, plbRegret ξ 𝒜 A T0 ω ≤
        2 * Real.sqrt (2 * d * T0 * betaTilde C1 amax lam d δ T0 *
          Real.log ((d * lam + T0 * amax ^ 2) / (d * lam))) + 2 * amax * Cp * T0 + 2 * d := by sorry

end LuoSunLiu.DIP
