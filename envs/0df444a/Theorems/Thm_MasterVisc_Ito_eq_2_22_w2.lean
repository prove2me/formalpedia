-- Prove2me | Theorems.Thm_MasterVisc_Ito_eq_2_22_w2
-- name    : MasterVisc.Ito.eq_2_22_w2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:38:16.149585+00:00
-- url     : https://prove2.me/theorems/645c1061-768f-4b50-b019-575192e97f54
-- title:
--   After (2.22), p. 945 — 𝒲₂(μⁿ_{[0,t_i]}, μ_{[0,t]}) + 𝒲₂(μ^{n,θ}_{[0,t_{i+1}]}, μ_{[0,t]}) → 0
-- statement:
--   Let $L>0$, let $\mu\in\widehat{\mathcal P}_L$ be represented as $\mu=\tilde{\mathbb P}\circ\tilde X^{-1}$, and use the discretizations of the proof of Theorem 2.7. For every $t\in[0,T)$ and $\theta\in[0,1]$, with $i=i(n,t)$ such that $t_i\le t<t_{i+1}$,
--   $$
--   \mathcal W_2\big(\mu^n_{[0,t_i]},\mu_{[0,t]}\big)+\mathcal W_2\big(\mu^{n,\theta}_{[0,t_{i+1}]},\mu_{[0,t]}\big)\longrightarrow0\qquad(n\to\infty),
--   $$
--   where $\mathcal W_2$ is the 2-Wasserstein distance (2.1) on laws on $\widehat\Omega$ with the Skorokhod distance as cost.
--
--   This is the convergence of the measure arguments that, with the continuity of the derivatives of $f$, gives the four limits on p. 946.
--
--   **Formalization Note** As for (2.22), the statement is made for $t<T$ with $i(n,t)=\lfloor nt/T\rfloor$. Distances are valued in $[0,\infty]$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), proof of Theorem 2.7, display after (2.22), p. 945

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_MasterVisc_Ito_Setting
import Definitions.Def_MasterVisc_Ito_Derivatives
import Definitions.Def_MasterVisc_Ito_Discretization
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

theorem eq_2_22_w2 {d : ℕ} {T : ℝ≥0}
    (L : ℝ) (hL : 0 < L) (μ : Measure (DPath d T)) (R : Rep d T) (hR : InPLhat L μ R)
    (t : ℝ≥0) (ht : t < T) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ =>
        W2SK ((lawStep R n).map (stopD (grid T n (gridIdx T n t)))) (μ.map (stopD t))
        + W2SK ((lawTheta R n (gridIdx T n t) θ).map (stopD (grid T n (gridIdx T n t + 1))))
            (μ.map (stopD t)))
      atTop (𝓝 0) := by sorry

end MasterVisc.Ito
