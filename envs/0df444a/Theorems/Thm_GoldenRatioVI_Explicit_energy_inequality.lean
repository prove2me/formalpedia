-- Prove2me | Theorems.Thm_GoldenRatioVI_Explicit_energy_inequality
-- name    : GoldenRatioVI.Explicit.energy_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:30:59.157428+00:00
-- url     : https://prove2.me/theorems/2ecd339d-e0c5-463a-8a6f-db30270a679a
-- title:
--   Eq. (27) — the energy inequality of the Explicit Golden Ratio Algorithm
-- statement:
--   Let $\mathcal E$ be a finite-dimensional real inner product space, let $g$ satisfy (C2) (proper, convex, lower semicontinuous) and let $F$ be monotone on $\operatorname{dom} g$ (C3). Consider a run of Algorithm 1 with parameter $\phi\in(1,\varphi]$, stepsizes $(\lambda_k)$, ratios $(\theta_k)$ and iterates $(z^k),(\bar z^k)$, and write $\Psi(u,v)=\langle F(u),v-u\rangle+g(v)-g(u)$. For every $z\in\operatorname{dom} g$ and every $k\ge 2$,
--   $$\frac{\phi}{\phi-1}\|\bar z^{k+1}-z\|^2 + \frac{\theta_k}{2}\|z^{k+1}-z^k\|^2 + 2\lambda_k\Psi(z,z^k) \le \frac{\phi}{\phi-1}\|\bar z^k-z\|^2 + \frac{\theta_{k-1}}{2}\|z^k-z^{k-1}\|^2 - \theta_k\|z^k-\bar z^k\|^2. \tag{27}$$
--
--   Taking $z=z^*\in S$, where $\Psi(z^*,z^k)\ge0$, this is the Lyapunov inequality that gives boundedness of the iterates and $\theta_k\|z^k-\bar z^k\|^2\to0$ in the proof of Theorem 2.
--
--   **Formalization Note** The paper says "let $z\in\mathcal E$ be arbitrary"; the statement is restricted to $z\in\operatorname{dom} g$, where $F(z)$ is defined and $\Psi(z,z^k)$ is a real number. The range $k\ge2$ is where the proof applies: it uses that $z^k$ is itself a proximal step, which holds from $k=2$ on.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 7, Eq. (27) (proof of Theorem 2)

import Mathlib
import Definitions.Def_GoldenRatioVI_Explicit_viProblem
import Definitions.Def_GoldenRatioVI_Explicit_egraalRun

namespace GoldenRatioVI.Explicit

/-- Eq. (27) of Malitsky (p. 7), the energy inequality of Algorithm 1: under (C2) and (C3),
for every `u ∈ dom g` and every `k ≥ 2`,
`(ϕ/(ϕ−1))‖z̄^{k+1} − u‖² + (θ_k/2)‖z^{k+1} − z^k‖² + 2λ_k Ψ(u, z^k)
  ≤ (ϕ/(ϕ−1))‖z̄^k − u‖² + (θ_{k−1}/2)‖z^k − z^{k−1}‖² − θ_k‖z^k − z̄^k‖²`. -/
theorem energy_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOnDom g F)
    (hrun : IsEGRAALRun g F ϕ lamBar z zbar lam theta)
    (u : E) (hu : u ∈ dom g) (k : ℕ) (hk : 2 ≤ k) :
    ϕ / (ϕ - 1) * ‖zbar (k + 1) - u‖ ^ 2 + theta k / 2 * ‖z (k + 1) - z k‖ ^ 2
        + 2 * lam k * psi g F u (z k) ≤
      ϕ / (ϕ - 1) * ‖zbar k - u‖ ^ 2 + theta (k - 1) / 2 * ‖z k - z (k - 1)‖ ^ 2
        - theta k * ‖z k - zbar k‖ ^ 2 := by sorry

end GoldenRatioVI.Explicit
