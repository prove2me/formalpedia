-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_dini_derivative_bound
-- name    : NonuniformKuramoto.CondI.dini_derivative_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:33.485396+00:00
-- url     : https://prove2.me/theorems/7e31789e-919c-4f28-8d1e-949e17ce92ec
-- title:
--   Proof of Theorem V.3, p. 22 — $\dot\theta_m-\dot\theta_\ell\le\max_{i\ne j}|\omega_i/D_i-\omega_j/D_j|-\Gamma_{\min}\sin\gamma+2\max_i\sum_jb_{ij}$
-- statement:
--   Consider the non-uniform Kuramoto model (8) with $n\ge2$, $D_i>0$, a complete coupling graph ($P_{ij}>0$ for $i\ne j$), $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$ and $P_{ii}=\varphi_{ii}=0$. Let $\theta\in\mathbb R^n$ be a configuration and $m,\ell$ indices with $\theta_\ell\le\theta_k\le\theta_m$ for all $k$ and $\theta_m-\theta_\ell=\gamma\in[0,\pi]$: all phases lie in the arc of length $\gamma$ from $\theta_\ell$ to $\theta_m$. With $\dot\theta_i$ the right-hand side of (8) divided by $D_i$ and $b_{ij}=P_{ij}\sin(\varphi_{ij})/D_i$,
--
--   $$\dot\theta_m-\dot\theta_\ell\ \le\ \max_{i\neq j}\Big|\frac{\omega_i}{D_i}-\frac{\omega_j}{D_j}\Big|-n\min_{i\ne j}\Big\{\frac{P_{ij}}{D_i}\cos(\varphi_{ij})\Big\}\sin(\gamma)+2\max_{i\in\{1,\dots,n\}}\sum_{j=1}^nb_{ij}.$$
--
--   The left-hand side is the upper Dini derivative of the arc length $V(\theta)=\theta_m-\theta_\ell$ along (8) when $m,\ell$ are the extreme indices; the right-hand side equals $\cos(\varphi_{\max})\Gamma_{\mathrm{critical}}-\Gamma_{\min}\sin\gamma$, so the arc cannot grow when (30) holds.
--
--   **Formalization Note** The pointwise inequality is stated for any extreme pair $m,\ell$, without the Dini derivative. $m=\ell$ (so $\gamma=0$) is allowed. The step does not use $P=P^T$, which is therefore not assumed.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 22, proof of Theorem V.3, second display (bound on D⁺V(θ(t)) in (29)); abbreviations a_ik, b_ik on p. 21

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- Proof of Theorem V.3, p. 22: if all angles of a lift `θ` lie between `θ_ℓ` and `θ_m`, with
`θ_m − θ_ℓ = γ ∈ [0, π]`, then
`θ̇_m − θ̇_ℓ ≤ max_{i≠j} |ω_i/D_i − ω_j/D_j| − Γ_min sin(γ) + 2 max_i ∑_j (P_ij/D_i) sin(ϕ_ij)`. -/
theorem dini_derivative_bound {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (θ : Fin n → ℝ) (m ℓ : Fin n) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγπ : γ ≤ Real.pi)
    (hmℓ : θ m - θ ℓ = γ) (hk : ∀ k, θ ℓ ≤ θ k ∧ θ k ≤ θ m) :
    field D ω P ϕ θ m - field D ω P ϕ θ ℓ ≤
      omegaSpread D ω - GammaMin D P ϕ * Real.sin γ + 2 * lossMax D P ϕ := by sorry

end NonuniformKuramoto.CondI
