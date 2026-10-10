-- Prove2me | Theorems.Thm_MasterVisc_Ito_theorem_2_7
-- name    : MasterVisc.Ito.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:37:47.793403+00:00
-- url     : https://prove2.me/theorems/54f338e3-9bbf-41de-be2e-01866fb13203
-- title:
--   Theorem 2.7, p. 945 — functional Itô formula (2.20) for f ∈ C_b^{1,1,1}(Θ̂) along μ ∈ 𝒫̂_L
-- statement:
--   Let $f\in C^{1,1,1}_b(\widehat\Theta)$ and $\mu\in\widehat{\mathcal P}_L$ for some $L>0$. Then for every $t\in[0,T]$,
--   $$
--   f(t,\mu)=f(0,\mu)+\int_0^t\partial_tf(s,\mu)\,ds+\mathbb E^\mu\Big[\int_0^t\partial_\mu f(s,\mu,\widehat X)\cdot d\widehat X_s+\frac12\int_0^t\partial_\omega\partial_\mu f(s,\mu,\widehat X):d\langle\widehat X\rangle_s\Big].\tag{2.20}
--   $$
--   Concretely: for every representation $\mu=\tilde{\mathbb P}\circ\tilde X^{-1}$ with $\tilde X_s=\tilde X_0+\int_0^s\tilde b_r\,dr+\int_0^s\tilde\sigma_r\,d\tilde B_r$, $|\tilde b|\le L$, $\tfrac12|\tilde\sigma|^2\le L$, $\tilde X_0\in\mathbb L^2(\tilde{\mathcal F}_0)$,
--   $$
--   f(t,\mu)=f(0,\mu)+\int_0^t\partial_tf(s,\mu)\,ds+\mathbb E^{\tilde{\mathbb P}}\Big[\int_0^t\Big(\partial_\mu f(s,\mu,\tilde X)\cdot\tilde b_s+\frac12\,\partial_\omega\partial_\mu f(s,\mu,\tilde X):\tilde\sigma_s\tilde\sigma_s^{\top}\Big)ds\Big].
--   $$
--
--   This is the functional Itô formula on the Wasserstein space of path laws: it extends the Itô formula (2.3) of Buckdahn–Li–Peng–Rainer and Chassagneux–Crisan–Delarue to path-dependent functions of the law, and it is the tool that links master equations to McKean–Vlasov dynamics in the rest of the paper.
--
--   **Formalization Note** The second display is (2.20) written in drift form: under the representation $d\widehat X=\tilde b\,ds+\tilde\sigma\,d\tilde B$ and $d\langle\widehat X\rangle=\tilde\sigma\tilde\sigma^\top ds$, and the expectation of $\int_0^t\partial_\mu f\cdot\tilde\sigma\,d\tilde B$ is zero because its integrand is square integrable ((2.19), bounded $\tilde\sigma$, $\mu\in\widehat{\mathcal P}_2$). It is stated for every representation of $\mu$; the left-hand side depends only on $\mu$. $A:B=\sum_{ij}A_{ij}B_{ij}$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 2.7 and (2.20), p. 945

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_MasterVisc_Ito_Setting
import Definitions.Def_MasterVisc_Ito_Derivatives
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

theorem theorem_2_7 {d : ℕ} {T : ℝ≥0} (Φ : C111DataD d T) (hΦ : IsC111bD Φ)
    (L : ℝ) (hL : 0 < L) (μ : Measure (DPath d T)) (R : Rep d T) (hR : InPLhat L μ R)
    (t : ℝ≥0) (ht : t ≤ T) :
    Φ.fn t μ = Φ.fn 0 μ + (∫ s in (0 : ℝ)..(t : ℝ), Φ.dt s.toNNReal μ)
      + ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ),
          (inner ℝ (Φ.dmu s.toNNReal μ (embed (R.Y ω))) (R.b s.toNNReal ω)
            + MasterVisc.Comparison.fdot (Φ.dwdmu s.toNNReal μ (embed (R.Y ω)))
                (R.σ s.toNNReal ω * (R.σ s.toNNReal ω).transpose) / 2)) ∂(R.P) := by sorry

end MasterVisc.Ito
