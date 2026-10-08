-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_theorem_4_i
-- name    : ManyServerQED.Scheduling.theorem_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:47:01.910512+00:00
-- url     : https://prove2.me/theorems/c16b10d1-bbdc-4224-a66d-a6104badbf73
-- title:
--   Theorem 4(i) — asymptotic lower bound: $\liminf_n E\int e^{-\gamma t}L(\hat X^n_t,u^n_t)\,dt\ge V(x)$
-- statement:
--   Let Assumptions 1(i), 2 and 3 hold and $\gamma>0$. Let $X^{0,n}\in\mathbb Z^k_+$ with $\hat X^{0,n}\to x\in\mathbb R^k$, and let $(\Psi^n,X^n)$ be a sequence of work-conserving admissible SCPs started from $X^{0,n}$. Fix $u_0\in\mathbb S^k$, and let $u^n=\Phi^n/(\mathbb 1\cdot X^n-n)^+$ when $\mathbb 1\cdot X^n>n$ and $u^n=u_0$ otherwise (47). Then
--   $$
--   \liminf_{n\to\infty}E\int_0^\infty e^{-\gamma t}L(\hat X^n_t,u^n_t)\,dt\ge V(x),
--   $$
--   where $V$ is the value of the diffusion control problem with data $\ell_i=\hat\lambda_i-\rho_i\hat\mu_i$, $\mu_i$, $\theta_i$, $r_i=(\lambda_iC^2_{U,i}+\lambda_i)^{1/2}$ and cost $L$ from (21).
--
--   This is the lower-bound half of asymptotic optimality: no work-conserving admissible policy beats the diffusion value in the limit.
--
--   **Formalization Note** Costs and $V$ are in $[0,\infty]$, with the liminf taken there. The initial states are integer vectors with $\hat X^{0,n}\to x$; the paper's literal "$\hat X^{0,n}\in n^{-1/2}\mathbb Z^k$" would require $\rho_in\in\mathbb Z$. Assumption 1(ii) is not imposed.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 31, Theorem 4(i)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Theorem 4(i) (p. 31): under Assumptions 1–3, for every sequence of work-conserving admissible
SCPs started from `X^{0,n}` with `X̂^{0,n} → x`, and `uⁿ` given by (47),
`liminf_n E ∫₀^∞ e^{−γt} L(X̂ⁿ_t, uⁿ_t) dt ≥ V(x)`. -/
theorem theorem_4_i {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n)) :
    value M.diffData (costOfTilde Lt) γ x ≤
      liminf (fun n => M.queueCostL (costOfTilde Lt) γ n u0 (X n) (Ψ n)) atTop := by sorry

end ManyServerQED.Scheduling
