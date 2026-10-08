-- Prove2me | Theorems.Thm_LinParamBandits_UEFinite_chernoff_finite_arms
-- name    : LinParamBandits.UEFinite.chernoff_finite_arms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:32.048007+00:00
-- url     : https://prove2.me/theorems/52cefcb1-1209-482a-822f-defb49f39cd1
-- title:
--   Theorem B.1 — Chernoff inequality for uncertainty ellipsoids with finitely many arms
-- statement:
--   Consider the linearly parameterized bandit of Rusmevichientong and Tsitsiklis under Assumption 1, with a finite nonempty set of arms $\mathcal U_r \subset \mathbb R^r$ ($r \ge 2$), run by the Uncertainty Ellipsoid policy. Let $\widehat Z_t$ be the least squares estimate and $C_t$ the inverse Gram matrix after $t$ periods, and $U_{t+1}$ the arm chosen next. For any $t \ge r$, $x, z \in \mathbb R^r$ and $\zeta > 0$,
--   $$\Pr\Big\{x'(\widehat Z_t - z) > \zeta\sigma_0\|x\|_{C_t} \;\Big|\; Z = z\Big\} \le t^{5|\mathcal U_r|}e^{-\zeta^2/2}$$
--   and
--   $$\Pr\Big\{(U_{t+1} - x)'(\widehat Z_t - z) > \zeta\sigma_0\|U_{t+1} - x\|_{C_t} \;\Big|\; Z = z\Big\} \le t^{5|\mathcal U_r|}e^{-\zeta^2/2}.$$
--
--   This extends the classical Chernoff bound to least squares estimates built from adaptively chosen arms; the price of adaptivity is the factor $t^{5|\mathcal U_r|}$. It is one of the two deviation inequalities from which the uncertainty radius is calibrated (Lemma B.6).
--
--   **Formalization Note** "Given $Z = z$" is the probability under the history law with the parameter fixed to $z$. The arm set is finite by the standing assumption of this mission (the paper remarks that the bound is vacuous for infinitely many arms); $|\mathcal U_r|$ is `𝒰.ncard`.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Theorem B.1, p. 29

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

theorem chernoff_finite_arms
    (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite) (h𝒰ne : 𝒰.Nonempty)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (hν : IsMarkovKernel ν) (hnoise : NoiseAssumption 𝒰 ν σ₀)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (harms : ArmAssumption 𝒰 b ū lam₀)
    (ψ : LinParamBandits.UEGeneral.Policy r) (hψ : IsUE 𝒰 b σ₀ ū lam₀ ψ)
    (t : ℕ) (ht : r ≤ t) (x z : LinParamBandits.LowerBound.Vec r) (ζ : ℝ) (hζ : 0 < ζ) :
    LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ x (LinParamBandits.UEGeneral.Zhat h - z) > ζ * σ₀ * normC h x} ≤
        ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2)) ∧
    LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ (ψ.act t h - x) (LinParamBandits.UEGeneral.Zhat h - z) >
        ζ * σ₀ * normC h (ψ.act t h - x)} ≤
        ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2)) := by sorry

end LinParamBandits.UEFinite
