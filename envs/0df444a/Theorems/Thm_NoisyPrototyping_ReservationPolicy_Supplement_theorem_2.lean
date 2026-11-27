-- Prove2me | Theorems.Thm_NoisyPrototyping_ReservationPolicy_Supplement_theorem_2
-- name    : NoisyPrototyping.ReservationPolicy.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:47:36.073051+00:00
-- url     : https://prove2.me/theorems/aa304b1d-0cdb-422e-b57f-5a1b9754cee1
-- title:
--   Theorem 2, p. 12 — Gaussian case: the explicit fidelity-adjusted reservation prices R_i and values p_i give the optimal evaluation and stopping policy
-- statement:
--   Consider $N$ independent prototypes. Prototype $i$ has a true value $P_i\sim\mathcal N(\mu_i,\sigma_i^2)$ with $\mu_i\in\mathbb R$ and $\sigma_i>0$, and evaluating it at cost $w_i>0$ reveals the measurement $m_i=P_i+\epsilon_i$, where $\epsilon_i\sim\mathcal N(0,1/\tau_i^2)$ is independent of $P_i$ and the fidelity is $\tau_i\in(0,\infty]$ ($\tau_i=\infty$ is perfect measurement, $m_i=P_i$). The firm sees only measurements, evaluates prototypes one at a time in any order, may stop at any time, and launches one evaluated prototype (receiving its true value) or nothing (receiving $0$); its net payoff is that value minus the costs paid.
--
--   Let $R(w)$ be the solution of $x=\mathbb E[\max\{x,Z\}]-w$ for $w>0$, where $Z$ is standard normal. Define
--   $$R_i=\mu_i+\frac{\sigma_i}{\sqrt{1+1/(\tau_i\sigma_i)^2}}\,R\!\left(\frac{w_i\sqrt{1+1/(\tau_i\sigma_i)^2}}{\sigma_i}\right),\qquad p_i=\mu_i+(m_i-\mu_i)\,\frac{1}{1+1/(\tau_i\sigma_i)^2},$$
--   and $p_0=0$. Reorder the prototypes so that $R_1\ge R_2\ge\cdots\ge R_N$ (ties in any way).
--
--   **Theorem.** The policy that, after $n$ evaluations ($0\le n\le N$),
--
--   1. continues iff $\max_{0\le i\le n}p_i<R_{n+1}$, and then evaluates prototype $n+1$;
--   2. stops iff $\max_{0\le i\le n}p_i\ge R_{n+1}$ (always when $n=N$), and then launches $k=\arg\max_{0\le i\le n}p_i$ (nothing if $k=0$),
--
--   is admissible, and for every admissible adaptive policy $\rho$
--   $$\mathbb E[\text{net payoff of }\rho]\le\mathbb E[\text{net payoff of this policy}].$$
--
--   The theorem makes the general optimal policy explicit for normal priors and normal noise: the order depends on each prototype's mean, uncertainty, fidelity and cost through one closed-form index, and the stopping rule compares a shrunken measurement with the next index.
--
--   **Formalization Note** The policy is the published `fidelityPolicy` with values $p_i$ and indices $R_i$; its running maximum starts at $0$ (the outside option $p_0$) and its argmax prefers the later prototype on ties. `Rstd` is any function whose value at each $x>0$ solves the defining equation of $R(x)$; the solution is unique, so this is the paper's $R$ on the arguments used.
--
--   Differences from the source:
--   - encoding: fidelity τ_i, with perfect measurement at τ = ∞ and the reciprocal 1/(τ_iσ_i) in the formulas → τ_i : ℝ≥0∞ with τ_i ≠ 0, and 1/τ_i read as (τ_i⁻¹).toNNReal, which is 0 at τ_i = ∞; reason: p. 12 expressly includes τ = ∞; τ_i = 0 would make every formula undefined, so the condition excludes only undefined cases
--   - encoding: σ_i, the standard deviation of P_i → a real σ_i with 0 < σ_i; reason: the formulas divide by σ_i and use it as a scale; σ_i = 0 is undefined in them and a negative σ_i is not a standard deviation
--   - encoding: (P_i, m_i) jointly normal with mean (μ_i, μ_i) and the printed covariance, m_i = P_i + ϵ_i → the push-forward of N(μ_i, σ_i²) ⊗ N(0, 1/τ_i²) under (P, ϵ) ↦ (P, P + ϵ), independent across prototypes through the published product outcome law; reason: this is exactly the printed joint law; independence across prototypes is the published model's disclosed reading
--   - reading: "Let R(w) be the solution of x = E[max{x, Z}] − w" → a function Rstd with Rstd(x) solving that equation for every x > 0; reason: the solution is unique, so Rstd agrees with the paper's R at every argument w_i√(1+1/(τ_iσ_i)²)/σ_i, all of which are positive; it is a hypothesis, not a chosen root
--   - reading: "the optimal dynamic policy after n evaluations is to (i) continue iff … (ii) stop iff …" → the policy with these two branches is admissible and its expected net payoff is at least that of every admissible adaptive policy; reason: the iff clauses describe the optimal rule, not strict suboptimality of the other action at a tie; same reading as the published Theorem 1
--   - encoding: "reorder the prototypes in the decreasing order of R_i", "k = arg max_{i≤n} p_i", p_0 = 0, the step n = N → a permutation ord with nonincreasing indices (ties in any way); the published running maximum V starting at 0 and its argmax B (none = launch nothing, later prototype on ties); stop at n = N; reason: the published model's conventions; any argmax attains the same maximum, and R_{N+1} is undefined
--   - encoding: costs w_i, one evaluation per prototype, admissible policies → 0 < w_i; each prototype evaluated at most once; admissible = measurable decision events and integrable net payoff; reason: inherited disclosed conventions of the published Model and Theorem 1
-- source:
--   Bhaskaran and Erat, Optimal Prototyping with Noisy Measurements, author manuscript of 6 Nov 2024 (MSOM 2025, doi:10.1287/msom.2024.1133), p. 12, Theorem 2 (proof pp. A2–A3, PDF 33–34)

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Supplement_Gaussian

namespace NoisyPrototyping.ReservationPolicy.Supplement
open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem theorem_2 {N : ℕ} (μ σ : Fin N → ℝ) (τ : Fin N → ℝ≥0∞) (w : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hτ : ∀ i, τ i ≠ 0) (hw : ∀ i, 0 < w i)
    (Rstd : ℝ → ℝ) (hRstd : ∀ x : ℝ, 0 < x → IsNormalRoot x (Rstd x))
    (ord : Fin N ≃ Fin N)
    (hord : ∀ a b, a ≤ b →
      gaussianIndex Rstd (μ (ord b)) (σ (ord b)) (τ (ord b)) (w (ord b)) ≤
        gaussianIndex Rstd (μ (ord a)) (σ (ord a)) (τ (ord a)) (w (ord a))) :
    Admissible (gaussianProblem μ σ τ w)
        (fidelityPolicy (fun i m => adjustedValue (μ i) (σ i) (τ i) m) ord
          (fun i => gaussianIndex Rstd (μ i) (σ i) (τ i) (w i))) ∧
    ∀ ρ : Policy N, Admissible (gaussianProblem μ σ τ w) ρ →
      value (gaussianProblem μ σ τ w) ρ ≤
        value (gaussianProblem μ σ τ w)
          (fidelityPolicy (fun i m => adjustedValue (μ i) (σ i) (τ i) m) ord
            (fun i => gaussianIndex Rstd (μ i) (σ i) (τ i) (w i))) := by sorry
end NoisyPrototyping.ReservationPolicy.Supplement
