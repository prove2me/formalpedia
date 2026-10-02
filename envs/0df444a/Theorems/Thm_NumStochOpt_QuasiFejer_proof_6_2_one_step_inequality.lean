-- Prove2me | Theorems.Thm_NumStochOpt_QuasiFejer_proof_6_2_one_step_inequality
-- name    : NumStochOpt.QuasiFejer.proof_6_2_one_step_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T20:40:05.368697+00:00
-- url     : https://prove2.me/theorems/3a0469d9-ddfd-43c5-b14d-0e1339b3ba7d
-- title:
--   Proof of Theorem 6.2, p. 145 — one-step inequality for the stochastic projection method
-- statement:
--   Let $X\subseteq\mathbb R^n$ be nonempty, closed and convex. Let $x^0,x^1,\dots$ and $\xi^0(s)$ be random vectors on a probability space, with $x^k$ measurable, $x^s$ square integrable and $\xi^0(s)$ integrable, and let $\rho_s$ be a random step size that is measurable with respect to $\sigma(x^0,\dots,x^s)$ and satisfies $E\{\rho_s^2\|\xi^0(s)\|^2\}<\infty$. Suppose one step of (6.11) is taken:
--   $$
--   x^{s+1}=\pi_X\big[x^s-\rho_s\xi^0(s)\big].
--   $$
--   Then for every $x^*\in X$, almost surely,
--   $$
--   E\{\|x^*-x^{s+1}\|^2\mid x^0,\dots,x^s\}\le\|x^*-x^s\|^2+2\rho_s\big\langle E\{\xi^0(s)\mid x^0,\dots,x^s\},x^*-x^s\big\rangle+E\{\rho_s^2\|\xi^0(s)\|^2\mid x^0,\dots,x^s\}.
--   $$
--
--   This is the first step of the proof of Theorem 6.2: combined with (6.12) it shows that the iterates form a stochastic quasi-Féjer sequence for $X^*$, and summed in expectation it gives the efficiency estimate for the weighted average.
--
--   **Formalization Note** The page prints the last term as $\rho_s E\{\|\xi^0(s)\|^2\mid\dots\}$; the exponent $2$ on $\rho_s$ is restored (the next display on the same page and (6.15) have $\rho_s^2$). Since $\rho_s$ is known at time $s$, $\rho_s^2$ is written inside the conditional expectation, which keeps the statement meaningful when only $\rho_s^2\|\xi^0(s)\|^2$, not $\|\xi^0(s)\|^2$, is integrable. The integrability hypotheses make all conditional expectations genuine (Lean returns $0$ for a non-integrable function).
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 145, Proof of Theorem 6.2, display 1

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.QuasiFejer

/-- **One-step inequality of the projection method** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988),
proof of Theorem 6.2, p. 145, first display). Let `X` be a nonempty closed convex set and
`x^{s+1} = π_X(x^s - ρ_s ξ⁰(s))` with `ρ_s` measurable with respect to `σ(x⁰, …, x^s)`. Then for
every `x* ∈ X`, almost surely,
`E{‖x* - x^{s+1}‖² | x⁰, …, x^s} ≤ ‖x* - x^s‖² + 2ρ_s⟨E{ξ⁰(s) | x⁰, …, x^s}, x* - x^s⟩
  + E{ρ_s² ‖ξ⁰(s)‖² | x⁰, …, x^s}`.
The page prints the last term as `ρ_s E{‖ξ⁰(s)‖² | …}`; the square on `ρ_s` is restored here
(it is `ρ_s²` in the next display and in (6.15)). -/
theorem proof_6_2_one_step_inequality {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ) (s : ℕ)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X) (hXne : X.Nonempty)
    (hx_meas : ∀ k, Measurable (x k)) (hx_L2 : MemLp (x s) 2 μ)
    (hξ_int : Integrable (ξ s) μ)
    (hρξ_int : Integrable (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ)
    (hρ_adapt : StronglyMeasurable[historySigma x s] (ρ s))
    (hrec : ∀ ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    condExp (historySigma x s) μ (fun ω => ‖xstar - x (s + 1) ω‖ ^ 2)
      ≤ᵐ[μ] fun ω => ‖xstar - x s ω‖ ^ 2
          + 2 * ρ s ω * ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ
          + (condExp (historySigma x s) μ (fun ω' => ρ s ω' ^ 2 * ‖ξ s ω'‖ ^ 2)) ω := by sorry

end NumStochOpt.QuasiFejer
