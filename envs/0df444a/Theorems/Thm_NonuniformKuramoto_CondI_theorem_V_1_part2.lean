-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_theorem_V_1_part2
-- name    : NonuniformKuramoto.CondI.theorem_V_1_part2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:12.47428+00:00
-- url     : https://prove2.me/theorems/e4062f25-f69e-4342-97e5-45f1056a31da
-- title:
--   Theorem V.1 2) — for $\varphi\equiv0$, $P=P^T$: $\dot\theta_\infty=\Omega$ with rate $\lambda_{fe}=\lambda_2(L(P_{ij}))\cos\gamma\cos(\angle(D\mathbf 1,\mathbf 1))^2/D_{\max}$
-- statement:
--   Assume the hypotheses of Theorem V.1 (model (8) with $n\ge2$, $D_i>0$, $P_{ij}\ge0$, $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$, $P_{ii}=\varphi_{ii}=0$, a globally reachable node, and $\bar\Delta(\gamma)$ positively invariant for some $\gamma\in[0,\pi/2-\varphi_{\max}[$), and moreover that all phase shifts vanish ($\varphi_{\max}=0$) and $P=P^T$. Put
--
--   $$\Omega:=\frac{\sum_i\omega_i}{\sum_iD_i},\qquad \lambda_{fe}:=\lambda_2(L(P_{ij}))\,\cos(\gamma)\,\cos(\angle(D\mathbf 1_n,\mathbf 1_n))^2/D_{\max}.$$
--
--   Then for every solution $\theta$ with $\theta(0)\in\bar\Delta(\gamma)$, every frequency $\dot\theta_i(t)$ converges to $\Omega$ as $t\to\infty$, and
--
--   $$\|\dot\theta(t)-\Omega\mathbf 1_n\|_2\le\sqrt{D_{\max}/D_{\min}}\;\|\dot\theta(0)-\Omega\mathbf 1_n\|_2\;e^{-\lambda_{fe}t}\qquad\text{for all }t\ge0.$$
--
--   The rate makes explicit how algebraic connectivity, phase cohesiveness and the non-uniformity of the time constants govern frequency synchronization.
--
--   **Formalization Note** Equation (19) prints $\lambda_{fe}$ with a leading minus sign, but the proof on p. 19 uses it as the positive decay rate in $e^{-\lambda_{fe}t}$; the positive rate is stated. The bound is the one the proof on p. 19 derives ($\sqrt{D_{\max}/D_{\min}}$ constant, Euclidean norm). The proof on p. 18 drops a factor $2$ and refers to (44) for (22); neither affects the statement. $\varphi_{\max}=0$ is written as $\varphi_{ij}=0$ for all $i,j$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 16, Theorem V.1 2) and (19); p. 19, end of the proof of Theorem V.1 (the rate bound)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

open Filter Topology

/-- Theorem V.1 2), p. 16, with the rate proved on p. 19: under the hypotheses of Theorem V.1, if
moreover all phase shifts vanish (`ϕ_max = 0`) and `P = Pᵀ`, then for every solution with
`θ(0) ∈ ∆̄(γ)` the frequencies converge to `Ω = ∑ ω_i / ∑ D_i`, and
`‖θ̇(t) − Ω 1‖₂ ≤ √(D_max / D_min) ‖θ̇(0) − Ω 1‖₂ e^{−λ_fe t}` for all `t ≥ 0`, with the positive
rate `λ_fe = λ₂(L(P_ij)) cos(γ) cos(∠(D1, 1))² / D_max`. -/
theorem theorem_V_1_part2 {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 ≤ P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (hreach : HasGloballyReachableNode P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ < Real.pi / 2 - phiMax ϕ)
    (hinv : IsPosInvariant D ω P ϕ (ArcClosed γ))
    (hϕ0 : ∀ i j, ϕ i j = 0) (hPsymm : ∀ i j, P i j = P j i)
    (θ : ℝ → Fin n → ℝ) (hθ : IsSolution D ω P ϕ θ) (h0 : ArcClosed γ (θ 0)) :
    (∀ i, Tendsto (fun t => field D ω P ϕ (θ t) i) atTop (𝓝 (Omega D ω))) ∧
    ∀ t : ℝ, 0 ≤ t →
      norm2 (fun i => field D ω P ϕ (θ t) i - Omega D ω) ≤
        Real.sqrt (Dmax D / Dmin D) * norm2 (fun i => field D ω P ϕ (θ 0) i - Omega D ω) *
          Real.exp (-(lambda2 (lap P) * Real.cos γ * cosAngleD D ^ 2 / Dmax D) * t) := by sorry

end NonuniformKuramoto.CondI
