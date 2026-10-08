-- Prove2me | Theorems.Thm_LinParamBandits_UEFinite_chernoff_infinite_arms
-- name    : LinParamBandits.UEFinite.chernoff_infinite_arms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:20.331745+00:00
-- url     : https://prove2.me/theorems/64c345d9-b2ea-4419-938d-686f151c6e74
-- title:
--   Theorem B.2 — Chernoff inequality for uncertainty ellipsoids, the t^{rκ₀²} form
-- statement:
--   Consider the linearly parameterized bandit of Rusmevichientong and Tsitsiklis under Assumption 1, with a compact nonempty set of arms $\mathcal U_r \subset \mathbb R^r$ ($r \ge 2$), finite or infinite, run by the Uncertainty Ellipsoid policy, and let $\kappa_0 = 2\sqrt{1 + \log(1 + 36\bar u^2/\lambda_0)}$. For any $t \ge r$, $x, z \in \mathbb R^r$ and $\zeta \ge 2$,
--   $$\Pr\Big\{x'(\widehat Z_t - z) > \zeta\kappa_0\sigma_0\sqrt{\log t}\,\|x\|_{C_t} \;\Big|\; Z = z\Big\} \le t^{r\kappa_0^2}e^{-\zeta^2/4}$$
--   and
--   $$\Pr\Big\{(U_{t+1} - x)'(\widehat Z_t - z) > \zeta\kappa_0\sigma_0\sqrt{\log t}\,\|U_{t+1} - x\|_{C_t} \;\Big|\; Z = z\Big\} \le t^{r\kappa_0^2}e^{-\zeta^2/4}.$$
--
--   The bound does not depend on the number of arms. For a finite arm set it is the inequality Lemma B.6 uses when $r\log t \le |\mathcal U_r|$, i.e. when Theorem B.1's factor $t^{5|\mathcal U_r|}$ is too large.
--
--   **Formalization Note** As on the page, the arm set is any compact nonempty set (the standing assumption of Sec. 1.1), not only a finite one. The power $t^{r\kappa_0^2}$ is a real power of $t \ge 2$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Theorem B.2, p. 30

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

theorem chernoff_infinite_arms
    (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰cpt : IsCompact 𝒰) (h𝒰ne : 𝒰.Nonempty)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (hν : IsMarkovKernel ν) (hnoise : NoiseAssumption 𝒰 ν σ₀)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (harms : ArmAssumption 𝒰 b ū lam₀)
    (ψ : LinParamBandits.UEGeneral.Policy r) (hψ : IsUE 𝒰 b σ₀ ū lam₀ ψ)
    (t : ℕ) (ht : r ≤ t) (x z : LinParamBandits.LowerBound.Vec r) (ζ : ℝ) (hζ : 2 ≤ ζ) :
    LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ x (LinParamBandits.UEGeneral.Zhat h - z) >
        ζ * kappa0 ū lam₀ * σ₀ * Real.sqrt (Real.log t) * normC h x} ≤
        ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * kappa0 ū lam₀ ^ 2) * Real.exp (-ζ ^ 2 / 4)) ∧
    LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ (ψ.act t h - x) (LinParamBandits.UEGeneral.Zhat h - z) >
        ζ * kappa0 ū lam₀ * σ₀ * Real.sqrt (Real.log t) * normC h (ψ.act t h - x)} ≤
        ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * kappa0 ū lam₀ ^ 2) * Real.exp (-ζ ^ 2 / 4)) := by sorry

end LinParamBandits.UEFinite
