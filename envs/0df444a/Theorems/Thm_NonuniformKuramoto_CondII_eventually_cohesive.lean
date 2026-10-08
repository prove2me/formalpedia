-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_eventually_cohesive
-- name    : NonuniformKuramoto.CondII.eventually_cohesive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:44.926843+00:00
-- url     : https://prove2.me/theorems/ad7665ef-685d-4108-a258-b9ee166b5e3a
-- title:
--   Proof of Theorem V.5, p. 26 — every trajectory from ‖Hθ(0)‖₂ < αγ_max eventually has ‖Hθ(t)‖_∞ ≤ ‖Hθ(t)‖₂ < π/2 − φ_max
-- statement:
--   Consider the non-uniform Kuramoto model (8) under the standing assumptions of §V.B ($n\ge2$, $D_i>0$, $P=P^T\ge0$ connected, $\varphi_{ij}=\varphi_{ji}\in[0,\pi/2[$, $P_{ii}=\varphi_{ii}=0$), assume condition (33), $\lambda_2(L(P_{ij}\cos\varphi_{ij}))>\lambda_{\mathrm{critical}}$, and let $\gamma_{\max}\in\,]\pi/2-\varphi_{\max},\pi]$ solve $\operatorname{sinc}(\gamma_{\max})/\operatorname{sinc}(\pi/2-\varphi_{\max})=\lambda_{\mathrm{critical}}/\lambda_2(L(P_{ij}\cos\varphi_{ij}))$. Then every solution with $\theta(0)\in\Delta(\pi)$ and $\|H\theta(0)\|_2<\alpha\gamma_{\max}$ admits $T\ge0$ such that for all $t\ge T$
--   $$
--   \|H\theta(t)\|_\infty\le\|H\theta(t)\|_2<\pi/2-\varphi_{\max}.
--   $$
--
--   Once the trajectory is in the arc $\bar\Delta(\gamma)$ with $\gamma<\pi/2-\varphi_{\max}$, frequency synchronization (Theorem V.1) applies; this is how statement 2) of Theorem V.5 is reached.
--
--   **Formalization Note** $\|H\theta\|_\infty=\max_{i,j}|\theta_i-\theta_j|$ is stated coordinatewise for the continuous lift. $\varphi_{ij}=\varphi_{ji}$ is a disclosed reading of the page.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 26, Proof of Theorem V.5, last paragraph

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Proof of Theorem V.5 (Dörfler–Bullo, arXiv:0910.5673v4, p. 26), last paragraph: under (33),
every solution of (8) with `θ(0) ∈ ∆(π)` and `‖Hθ(0)‖₂ < α γ_max` has a time `T ≥ 0` with
`‖Hθ(t)‖_∞ ≤ ‖Hθ(t)‖₂ < π/2 − ϕ_max` for all `t ≥ T`. -/
theorem eventually_cohesive {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hyp : StandingHyp D P ϕ)
    (hcrit : lambdaCritical D ω P ϕ < lambda2 (lossless P ϕ))
    (γmax : ℝ) (hγmax : γmax ∈ Set.Ioc (Real.pi / 2 - phiMax ϕ) Real.pi ∧
      Real.sinc γmax / Real.sinc (Real.pi / 2 - phiMax ϕ) =
        lambdaCritical D ω P ϕ / lambda2 (lossless P ϕ))
    (θ : ℝ → Fin n → ℝ) (hsol : NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ) (h0 : NonuniformKuramoto.CondI.ArcOpen Real.pi (θ 0))
    (h0γ : normH (θ 0) < alpha D * γmax) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t →
      (∀ i j, |θ t i - θ t j| ≤ normH (θ t)) ∧ normH (θ t) < Real.pi / 2 - phiMax ϕ := by sorry

end NonuniformKuramoto.CondII
