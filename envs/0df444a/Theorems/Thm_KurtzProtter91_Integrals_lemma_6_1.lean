-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_lemma_6_1
-- name    : KurtzProtter91.Integrals.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:15:49.006491+00:00
-- url     : https://prove2.me/theorems/ecd1fa6f-5be1-4e5d-993d-ae8d0b0e35ea
-- title:
--   Lemma 6.1 — z_n → z implies (z_n, I_ε(z_n)) → (z, I_ε(z)) a.s. in the Skorohod topology
-- statement:
--   Let $E$ be a metric space, $\varepsilon>0$, and let $I_\varepsilon=I^\theta_\varepsilon$ be the step approximation of §6, driven by a sequence $\theta=(\theta_k)$ of independent random variables uniformly distributed on $[\tfrac12,1]$. If $z_n\to z$ in the Skorohod topology on $D_E[0,\infty)$, then, for almost every $\theta$,
--   $$(z_n,I^\theta_\varepsilon(z_n))\to(z,I^\theta_\varepsilon(z))\quad\text{in the Skorohod topology on }D_{E\times E}[0,\infty).$$
--
--   Lemma 6.1 provides the step approximation $X_n^\varepsilon$ of the integrand that converges in distribution along with $(X_n,Y_n)$ in the proof of Theorem 2.2.
--
--   **Formalization Note** "a.s." refers to the law of $\theta$, the infinite product of the uniform distribution on $[\tfrac12,1]$. The exceptional null set may depend on the convergent sequence $(z_n)$ and on $z$: the order of quantifiers is the page's, "for every convergent sequence, almost surely".
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1067, Lemma 6.1

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod
import Definitions.Def_KurtzProtter91_Integrals_StepApprox

open Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem lemma_6_1 {E : Type*} [MetricSpace E] (ε : ℝ) (hε : 0 < ε) (zs : ℕ → ℝ≥0 → E)
    (z : ℝ≥0 → E) (h : SkorohodTendsto zs z) :
    ∀ᵐ θ ∂thetaLaw, SkorohodTendsto (fun n t => (zs n t, stepApprox ε θ (zs n) t))
      (fun t => (z t, stepApprox ε θ z t)) := by sorry

end KurtzProtter91.Integrals
