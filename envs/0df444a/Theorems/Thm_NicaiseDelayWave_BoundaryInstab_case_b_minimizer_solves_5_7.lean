-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryInstab_case_b_minimizer_solves_5_7
-- name    : NicaiseDelayWave.BoundaryInstab.case_b_minimizer_solves_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T21:09:16.273378+00:00
-- url     : https://prove2.me/theorems/6646b1ec-eab1-421a-b46d-e5fb8988354a
-- title:
--   Case (b), μ2 > μ1 — a minimiser φ of s·q0 + √(s²q0² + 4q1) on the unit sphere solves (5.7) with 2b = its minimum value
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N, d\Gamma)$ be a mixed domain, let $0 < \mu_1 < \mu_2$, and put $s = \sqrt{\mu_2^2-\mu_1^2}$. Let $\mathcal V$ be the class of real functions that are $C^2$ in $\Omega$, $C^1$ on $\overline\Omega$ and vanish on $\Gamma_D$, and for $w \in \mathcal V$ let
--   $$q_0(w) = \int_{\Gamma_N} |w|^2\,d\Gamma, \qquad q_1(w) = \int_\Omega |\nabla w|^2\,dx, \qquad B(w) = s\,q_0(w) + \sqrt{s^2 q_0(w)^2 + 4q_1(w)} .$$
--   Suppose that $\varphi \in \mathcal V$ with $\int_\Omega \varphi^2\,dx = 1$ attains the minimum of $B$ over $\{w \in \mathcal V : \int_\Omega w^2\,dx = 1\}$, as in (5.16), and let $b = B(\varphi)/2$, as in (5.15). Then $\varphi$ solves (5.7):
--   $$\int_\Omega \nabla\varphi\cdot\nabla v\,dx - b^2\int_\Omega \varphi v\,dx + b\sqrt{\mu_2^2-\mu_1^2}\int_{\Gamma_N}\varphi v\,d\Gamma = 0 \qquad \text{for every } v \in \mathcal V.$$
--
--   This is case (b) of §5.1: together with the choice of delays (5.5)–(5.6), (5.7) is the variational form of (5.2) at $\lambda = ib$, so the minimiser produces a solution $e^{ibt}\varphi$ with constant standard energy for each delay $\tau = (\arccos(-\mu_1/\mu_2) + 2l\pi)/b$.
--
--   **Formalization Note** The paper minimises over the unit sphere of $H^1_{\Gamma_D}(\Omega)$ and tests (5.7) against all of $H^1_{\Gamma_D}(\Omega)$; the statement uses the classical class $\mathcal V$ in both places, since Sobolev spaces on domains are not available in Mathlib. As in the paper, the existence of the minimiser is a hypothesis ("if the minimum … is attained at $\varphi$"), not a conclusion. Functions are real, so the complex conjugates $\bar v$ of the page disappear.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), pp. 1580–1582, §5.1, Case (b), (5.11), (5.15)–(5.19), (5.7)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryInstab_DelayProblem

open MeasureTheory

namespace NicaiseDelayWave.BoundaryInstab

/-- Case (b), (5.15)–(5.19): let `0 < μ₁ < μ₂` and `s = √(μ₂² - μ₁²)`. If `φ` in the admissible
class, with `∫_Ω φ² = 1`, minimises `B_s(w) = s q₀(w) + √(s² q₀(w)² + 4 q₁(w))` over the
normalised admissible functions, then with `b = B_s(φ)/2` the function `φ` solves (5.7):
`∫_Ω ∇φ·∇v dx - b² ∫_Ω φ v dx + b s ∫_{Γ_N} φ v dΓ = 0` for every admissible `v`. -/
theorem case_b_minimizer_solves_5_7 {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (μ1 μ2 : ℝ)
    (hμ1 : 0 < μ1) (hμ12 : μ1 < μ2)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : φ ∈ admissible D)
    (hnorm : ∫ x in D.Ω, φ x ^ 2 = 1)
    (hmin : ∀ w ∈ admissible D, ∫ x in D.Ω, w x ^ 2 = 1 →
      functionalB D (Real.sqrt (μ2 ^ 2 - μ1 ^ 2)) φ ≤
        functionalB D (Real.sqrt (μ2 ^ 2 - μ1 ^ 2)) w) :
    ∀ v ∈ admissible D,
      (∫ x in D.Ω, inner ℝ (gradient φ x) (gradient v x))
        - (functionalB D (Real.sqrt (μ2 ^ 2 - μ1 ^ 2)) φ / 2) ^ 2 * (∫ x in D.Ω, φ x * v x)
        + (functionalB D (Real.sqrt (μ2 ^ 2 - μ1 ^ 2)) φ / 2) * Real.sqrt (μ2 ^ 2 - μ1 ^ 2)
            * (∫ x in D.ΓN, φ x * v x ∂D.σ) = 0 := by sorry

end NicaiseDelayWave.BoundaryInstab
