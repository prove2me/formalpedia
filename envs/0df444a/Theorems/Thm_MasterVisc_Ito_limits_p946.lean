-- Prove2me | Theorems.Thm_MasterVisc_Ito_limits_p946
-- name    : MasterVisc.Ito.limits_p946
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:37:40.131956+00:00
-- url     : https://prove2.me/theorems/b5c387d0-c90a-4ba7-be3f-044994ca9359
-- title:
--   Proof of Theorem 2.7, p. 946 — the four limits of f(T, μⁿ) − f(0, μⁿ), I₁ⁿ, and the L² limits of the integrated ∂_μf and ∂_ω∂_μf terms
-- statement:
--   Let $f\in C^{1,1,1}_b(\widehat\Theta)$, $L>0$, let $\mu\in\widehat{\mathcal P}_L$ be represented as $\mu=\tilde{\mathbb P}\circ\tilde X^{-1}$, and use the discretizations of the proof of Theorem 2.7, with $I_1^n=\sum_{i<n}\int_{t_i}^{t_{i+1}}\partial_tf(t,\mu^n_{[0,t_i]})\,dt$. Then
--   $$
--   \lim_{n\to\infty}\big[f(T,\mu^n)-f(0,\mu^n)\big]=f(T,\mu)-f(0,\mu),\qquad\lim_{n\to\infty}I_1^n=\int_0^T\partial_tf(t,\mu)\,dt,
--   $$
--   and for every $t\in[0,T)$, with $i=i(n,t)$ such that $t_i\le t<t_{i+1}$,
--   $$
--   \lim_{n\to\infty}\mathbb E^{\tilde{\mathbb P}}\Big[\Big|\int_0^1\partial_\mu f\big(t_{i+1},\mu^{n,\theta},\tilde X^n_{t_i\wedge\cdot}\big)\,d\theta-\partial_\mu f(t,\mu,\tilde X)\Big|^2\Big]=0,
--   $$
--   $$
--   \lim_{n\to\infty}\mathbb E^{\tilde{\mathbb P}}\Big[\Big|\int_0^1\!\!\int_0^1\partial_\omega\partial_\mu f\big(t_{i+1},\mu^{n,\theta},\tilde X^{n,\tilde\theta\theta}\big)\,\theta\,d\tilde\theta\,d\theta-\tfrac12\,\partial_\omega\partial_\mu f(t,\mu,\tilde X)\Big|^2\Big]=0.
--   $$
--
--   Plugged into (2.21), these give the functional Itô formula (2.20). The $\tfrac12$ is $\int_0^1\theta\,d\theta$.
--
--   **Formalization Note** The last two limits are stated for $t<T$, where the index $i(n,t)=\lfloor nt/T\rfloor$ is defined. The expectations of squares are taken in $[0,\infty]$, so they cannot vanish by a junk value; the matrix norm is the Frobenius norm and the double integral of a matrix is taken entrywise.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), proof of Theorem 2.7, the four limits, p. 946

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_MasterVisc_Ito_Setting
import Definitions.Def_MasterVisc_Ito_Derivatives
import Definitions.Def_MasterVisc_Ito_Discretization
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

theorem limits_p946 {d : ℕ} {T : ℝ≥0} (Φ : C111DataD d T) (hΦ : IsC111bD Φ)
    (L : ℝ) (hL : 0 < L) (μ : Measure (DPath d T)) (R : Rep d T) (hR : InPLhat L μ R) :
    Tendsto (fun n : ℕ => Φ.fn T (lawStep R n) - Φ.fn 0 (lawStep R n)) atTop
      (𝓝 (Φ.fn T μ - Φ.fn 0 μ)) ∧
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
        ∫ s in (grid T n i : ℝ)..(grid T n (i + 1) : ℝ),
          Φ.dt s.toNNReal ((lawStep R n).map (stopD (grid T n i)))) atTop
      (𝓝 (∫ s in (0 : ℝ)..(T : ℝ), Φ.dt s.toNNReal μ)) ∧
    (∀ t : ℝ≥0, t < T →
      Tendsto (fun n : ℕ => ∫⁻ ω,
          ‖(∫ θ in (0 : ℝ)..1, Φ.dmu (grid T n (gridIdx T n t + 1))
                (lawTheta R n (gridIdx T n t) θ)
                (stopD (grid T n (gridIdx T n t)) (stepD n (R.Y ω))))
            - Φ.dmu t μ (embed (R.Y ω))‖ₑ ^ 2 ∂(R.P)) atTop (𝓝 0)) ∧
    (∀ t : ℝ≥0, t < T →
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (MasterVisc.Comparison.frob2
          ((Matrix.of fun a b => ∫ θ in (0 : ℝ)..1, ∫ θ' in (0 : ℝ)..1,
              θ * Φ.dwdmu (grid T n (gridIdx T n t + 1)) (lawTheta R n (gridIdx T n t) θ)
                (thetaD n (gridIdx T n t) (θ' * θ) (R.Y ω)) a b)
            - (1 / 2 : ℝ) • Φ.dwdmu t μ (embed (R.Y ω)))) ∂(R.P)) atTop (𝓝 0)) := by sorry

end MasterVisc.Ito
