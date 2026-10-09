-- Prove2me | Theorems.Thm_MKVDPP_Weak_theorem_3_1
-- name    : MKVDPP.Weak.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:27:34.107934+00:00
-- url     : https://prove2.me/theorems/c3dbbca6-59bb-4f28-80d3-10f27614fbae
-- title:
--   Theorem 3.1, p. 9 — V_W is upper semi-analytic and satisfies the dynamic programming principle (3.2)
-- statement:
--   Let $T>0$, $n,d,\ell\in\mathbb N$, $p\ge0$, $U$ a nonempty Polish space with metric $\rho$, $u_0\in U$, and $\pi:U\to[0,1]$ a Borel isomorphism onto its image. Let the coefficients $b,\sigma,\sigma_0,L,g$ be Borel measurable and $b,\sigma,\sigma_0,L$ non-anticipative. Let $V_W$ be the value function (2.5) of the weak McKean–Vlasov control problem.
--
--   1. The map $V_W:[0,T]\times\mathcal P(\mathcal C^n)\to[-\infty,\infty]$ is upper semi-analytic.
--   2. Let $(t,\nu)\in[0,T]\times\mathcal P(\mathcal C^n)$ and let $\tau^\star$ be a $\mathbb G^\star$-stopping time on $\Omega^\star$ with values in $[t,T]$. With $\tau^\gamma:=\tau^\star(B^{\gamma,t},\hat\mu^\gamma)$ as in (3.1),
--   $$V_W(t,\nu)=\sup_{\gamma\in\Gamma_W(t,\nu)}\mathbb E^{\mathbb P^\gamma}\Big[\int_t^{\tau^\gamma}L(s,X^\gamma_{s\wedge\cdot},\bar\mu^\gamma_s,\alpha^\gamma_s)\,ds+V_W\big(\tau^\gamma,\mu^\gamma_{\tau^\gamma}\big)\Big].$$
--
--   This is the dynamic programming principle for the McKean–Vlasov control problem with common noise in its weak formulation; the stopping rule is fixed once on the canonical space $\Omega^\star$ and transported to each control through the common noise and the conditional-law process.
--
--   **Formalization Note** The expectation and the time integral use the paper's convention $\infty-\infty:=-\infty$; in the sum inside the expectation, $(+\infty)+(-\infty)$ is also $-\infty$ (the page leaves that sum undefined). The integrand may fail to be measurable ($V_W$ is only u.s.a.); expectations are lower integrals of the positive and negative parts, which coincide with the completed integral for universally measurable integrands. $\mu^\gamma_{\tau^\gamma}$ is the $X$-marginal of $\hat\mu^\gamma_{\tau^\gamma}$. The supremum runs over weak controls on probability spaces in universe 0, with $\sup\emptyset=-\infty$. No integrability of $L,g$ and no Lipschitz condition is assumed, as on the page.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 9, Theorem 3.1, (3.1)–(3.2)

import Mathlib
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

/-- **Theorem 3.1** (p. 9). The value function `V_W` of the weak McKean–Vlasov control problem
(2.5) is upper semi-analytic on `[0,T] × 𝒫(𝒞ⁿ)`, and it satisfies the dynamic programming
principle (3.2) for every `𝔾⋆`-stopping time `τ⋆` with values in `[t,T]`, with
`τ^γ := τ⋆(B^{γ,t}, μ̂^γ)` (3.1). -/
theorem theorem_3_1
    {T : ℝ≥0} (hT : 0 < T) {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
    (u₀ : U) (p : ℝ) (hp : 0 ≤ p) (π : U → ℝ) (hπ : IsControlEncoding π)
    (c : Coeffs T n d ℓ U) (hc : c.IsAdmissible) :
    IsUpperSemianalytic
        (fun x : Set.Icc (0:ℝ≥0) T × ProbabilityMeasure (Cpath T n) => VW c u₀ p π x.1 x.2) ∧
      ∀ t : ℝ≥0, t ≤ T → ∀ ν : ProbabilityMeasure (Cpath T n),
        ∀ τstar : OmegaStar T n d ℓ → ℝ≥0,
          IsStoppingTime (GStar T n d ℓ) (fun ω => (τstar ω : WithTop ℝ≥0)) →
          (∀ ω, t ≤ τstar ω ∧ τstar ω ≤ T) →
          VW c u₀ p π t ν =
            ⨆ (Ω : Type) (mΩ : MeasurableSpace Ω)
              (γ : @WeakControl T n d ℓ U _ _ c u₀ p π Ω mΩ t ν),
              @dppReward T n d ℓ U _ _ c u₀ p π Ω mΩ t ν γ τstar := by sorry

end MKVDPP.Weak
