-- Prove2me | Theorems.Thm_MasterVisc_Ito_eq_2_22
-- name    : MasterVisc.Ito.eq_2_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:37:50.951994+00:00
-- url     : https://prove2.me/theorems/ea39a250-1fcc-4b3e-ac09-c30ed78d638d
-- title:
--   (2.22), p. 945 — d_SK(X̃ⁿ, X̃) + d_SK(X̃ⁿ_{t_i∧·}, X̃_{t∧·}) + d_SK(X̃^{n,θ}_{t_{i+1}∧·}, X̃_{t∧·}) → 0 a.s.
-- statement:
--   Let $L>0$, let $\mu\in\widehat{\mathcal P}_L$ be represented as $\mu=\tilde{\mathbb P}\circ\tilde X^{-1}$ (so $\tilde X$ is continuous), and use the discretizations of the proof of Theorem 2.7. For every $t\in[0,T)$ and $\theta\in[0,1]$, with $i=i(n,t)$ the index such that $t_i\le t<t_{i+1}$,
--   $$
--   d_{SK}(\tilde X^n,\tilde X)+d_{SK}(\tilde X^n_{t_i\wedge\cdot},\tilde X_{t\wedge\cdot})+d_{SK}(\tilde X^{n,\theta}_{t_{i+1}\wedge\cdot},\tilde X_{t\wedge\cdot})\longrightarrow0\quad(n\to\infty),\qquad\tilde{\mathbb P}\text{-a.s.}\tag{2.22}
--   $$
--
--   These pathwise convergences feed the dominated-convergence step that gives the $\mathcal W_2$ limits and the four limits of the proof.
--
--   **Formalization Note** The page says "for any $t\in[0,T]$"; at $t=T$ no index $i$ satisfies $t_i\le t<t_{i+1}$, so the statement is made for $t<T$, with $i(n,t)=\lfloor nt/T\rfloor$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), proof of Theorem 2.7, (2.22), p. 945

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_MasterVisc_Ito_Setting
import Definitions.Def_MasterVisc_Ito_Derivatives
import Definitions.Def_MasterVisc_Ito_Discretization
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

theorem eq_2_22 {d : ℕ} {T : ℝ≥0}
    (L : ℝ) (hL : 0 < L) (μ : Measure (DPath d T)) (R : Rep d T) (hR : InPLhat L μ R)
    (t : ℝ≥0) (ht : t < T) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂(R.P), Tendsto (fun n : ℕ =>
        dSK (stepD n (R.Y ω)) (embed (R.Y ω))
        + dSK (stopD (grid T n (gridIdx T n t)) (stepD n (R.Y ω))) (stopD t (embed (R.Y ω)))
        + dSK (stopD (grid T n (gridIdx T n t + 1)) (thetaD n (gridIdx T n t) θ (R.Y ω)))
            (stopD t (embed (R.Y ω))))
      atTop (𝓝 0) := by sorry

end MasterVisc.Ito
