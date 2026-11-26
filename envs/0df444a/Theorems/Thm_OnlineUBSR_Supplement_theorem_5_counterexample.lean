-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_theorem_5_counterexample
-- name    : OnlineUBSR.Supplement.theorem_5_counterexample
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:40:22.647801+00:00
-- url     : https://prove2.me/theorems/b43097e7-9565-482a-804e-e051091e1d2a
-- title:
--   Theorem 5 (corrected: counterexample to the printed unprojected bound)
-- statement:
--   Theorem 5 is false under its printed domain. On a one-point probability space take $\xi(\theta)=\theta^2$, $\ell(x)=e^x$, $\lambda=1$, and $\theta\in[1,2]$. Then $h(\theta)=\theta^2$, Assumptions 1–10 hold on the interval, and $h'_m(\theta)=2\theta$ for every positive batch size. With $\theta_0=\theta^*=1$ and $b=1$, the unprojected recursion gives $\theta_1=-1$ and $\theta_n=0$ for $n\ge2$. Consequently the squared error is one while the right side of (15) tends to zero as $n,m\to\infty$.
--
--   This counterexample isolates the missing invariant: (10) is unprojected although every curvature and derivative assumption is confined to $[\theta_l,\theta_u]$.
--
--   Differences from the source:
--   - correction: Theorem 5 asserts inequality (15) for the unprojected recursion under interval-local assumptions → Lean asserts an explicit instance satisfying Assumptions 1–10 that violates (15); reason: the update leaves the interval at the first step and the printed result is false
--   - correction: the exponent in (15) is $c^2L_4^2\pi^2/6$ → the tested bound uses $b^2L_4^2\pi^2/6$; reason: Corollary 1 on p.11 and the proof on p.28 both show that $c^2$ is a typographical error
--   - correction: $L_3$ is undefined → Lean uses $L_3=2$ as the bound on $|\xi''(\theta)|$; reason: this is the meaning used by Lemma 2's proof
--   - encoding: the paper says Assumptions 7 and 9 make $h$ smooth → Lean explicitly includes smoothness on the interval; reason: this prevents junk derivatives
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 5, p.10, equation (15); counterexample derived from (10), p.8

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR.Supplement

/-- **Counterexample to Theorem 5 (unprojected SGD leaves the assumption interval).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 5, p.10, (15),
with the recursion and proof on pp.27--29.

Take deterministic samples `ξ(θ)=θ²`, exponential loss, `λ=1`, and parameter interval
`[1,2]`. Then `h(θ)=SR₁(X(θ))=θ²`, all Assumptions 1--10 hold on `[1,2]`, and the derivative
estimator is exactly `2θ` for every positive batch size. With `θ₀=θ*=1` and `b=1`, the
unprojected recursion gives `θ₁=-1`, `θ₂=0`, and thereafter stays at zero. Hence the squared
error is one for every `n≥2`, whereas the corrected right side of (15), with `b²` in the
exponential, tends to zero as `n,m→∞`.

**Formalization Note.** This theorem existentially supplies horizons and batch sizes for which
the reverse of (15) holds while the formal predicates encoding every source assumption hold.
It does not add a projection or interior-minimizer premise because neither repair is stated or
supported by the source. -/
theorem theorem_5_counterexample :
    let μ : Measure Unit := Measure.dirac ()
    let M : Model Unit := {
      ν := Measure.dirac ()
      ℓ := Real.exp
      lam := 1
      tl := 0
      tu := 5
      t₀ := 0
      c := Real.exp 4
      M₀ := 4
      μ₁ := Real.exp (-4)
      L₁ := Real.exp 4
      σ := 1
      θl := 1
      θu := 2
      η := 1 / 2
      L₂ := Real.exp 4
      zeta := 1
      zetaTilde := 1
      M₂ := 4
      β₁ := 1
      F := fun θ _ => θ ^ 2 }
    let S : Bool → ℕ → ℕ → Unit → Unit := fun _ _ _ _ => ()
    ∃ n m : ℕ, 2 ≤ n ∧ 1 ≤ m ∧
      IsSampleBank μ M S ∧ Assumptions1To3 M ∧ Assumptions5To9 M ∧ SmoothObjective M ∧
      (∀ outer θ, θ ∈ Set.Icc M.θl M.θu → InnerNoiseBound μ M S outer θ) ∧
      (∀ θ ∈ Set.Icc M.θl M.θu,
        ∀ᵐ u ∂M.ν, |deriv (deriv (fun q => M.F q u)) θ| ≤ (2 : ℝ)) ∧
      (∀ θ ∈ Set.Icc M.θl M.θu, (1 : ℝ) < deriv (deriv (objective M)) θ) ∧
      (1 : ℝ) ∈ Set.Icc M.θl M.θu ∧
      (∀ θ ∈ Set.Icc M.θl M.θu, objective M 1 ≤ objective M θ) ∧
      Real.exp (1 ^ 2 * (L4 M 2) ^ 2 * Real.pi ^ 2 / 6) *
          (3 * ((1 : ℝ) - 1) ^ 2 / (n : ℝ) ^ (2 * 1 * 1) +
            3 * C5Uniform M m * (2 : ℝ) ^ (2 * 1 * 1) /
              ((2 * 1 * 1 - 1) * n) +
            3 * C5Uniform M m * (2 : ℝ) ^ (5 * 1 * 1) /
              ((1 * 1) ^ 2 * m)) <
        ∫ ω, (unprojectedSGD M S 1 1 m n ω - 1) ^ 2 ∂μ := by sorry

end OnlineUBSR.Supplement
