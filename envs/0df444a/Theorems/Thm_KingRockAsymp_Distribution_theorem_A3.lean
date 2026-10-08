-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_theorem_A3
-- name    : KingRockAsymp.Distribution.theorem_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:57.278849+00:00
-- url     : https://prove2.me/theorems/5656bfc3-4066-404d-83e1-2f09ee1f9fa1
-- title:
--   Theorem A3 — central limit theorem in $C_m(U)$ for Lipschitz integrands
-- statement:
--   Let $U \subseteq \mathbb R^n$ be compact and let $f : U \times S \to \mathbb R^m$ and the random elements $s_1, s_2, \dots$ of $S$ satisfy the probabilistic assumptions:
--
--   1. (P.1) $f$ is continuous in $x$ and measurable in $s$;
--   2. (P.2) the $s_i$ are independent and identically distributed;
--   3. (P.3) $E|f(x,s_1)|^2 < \infty$ for some $x \in U$;
--   4. (P.4) there is $a : S \to \mathbb R$ with $E|a(s_1)|^2 < \infty$ and $|f(x_1,s) - f(x_2,s)| \le a(s)|x_1 - x_2|$ for all $x_1, x_2 \in U$.
--
--   Let $\bar f^\nu = \frac1\nu\sum_{i=1}^\nu f(\cdot,s_i)$ and $Ef = E f(\cdot, s_1)$, both in $C_m(U)$. Then there exists a Gaussian random variable $w$ taking values in $C_m(U)$ such that
--   $$\sqrt\nu\,\big(\bar f^\nu - Ef\big) \xrightarrow{\ \mathcal D\ } w.$$
--
--   This is the functional central limit theorem for empirical means of Lipschitz integrands, uniformly over $x \in U$; it supplies the data convergence that Theorem 2.6 needs for M-estimates.
--
--   **Formalization Note** $f$ is encoded as `S → C(↥U, Rn m)`, so continuity in $x$ is part of the type. $Ef$ is the Bochner integral of $s \mapsto f(\cdot,s)$ in $C_m(U)$; under P.3–P.4 that map is integrable, and since evaluation at $x$ is a continuous linear map, the integral evaluated at $x$ is $E f(x,s_1)$, the paper's pointwise $Ef$. "Gaussian" is Mathlib's `IsGaussian` (every continuous linear functional has a real normal law), which is the Appendix's definition; the paper's statement does not specify the mean and covariance of $w$, and none is added. $s_1$ is `s 0`, and the sum runs over `Finset.range ν`. The limit law is given as a probability measure on $C_m(U)$, i.e. $w$ is the identity on $C_m(U)$ under that law.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), Appendix, Theorem A3, p. 16 (authors' manuscript pagination)

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

theorem theorem_A3 {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (f : S → C(↥U, Rn m))
    (hmeas : ∀ x : ↥U, Measurable (fun σ => f σ x))
    (s : ℕ → Ω → S) (hs : ∀ i, Measurable (s i))
    (hindep : iIndepFun s P) (hident : ∀ i, IdentDistrib (s i) (s 0) P P)
    (hP3 : ∃ x : ↥U, MemLp (fun ω => f (s 0 ω) x) 2 P)
    (hP4 : ∃ a : S → ℝ, MemLp (fun ω => a (s 0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ a σ * ‖(x₁ : Rn n) - x₂‖) :
    ∃ μG : ProbabilityMeasure C(↥U, Rn m), IsGaussian (μG : Measure C(↥U, Rn m)) ∧
      TendstoInDistribution
        (fun (ν : ℕ) ω => Real.sqrt ν •
          ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω) - ∫ ω', f (s 0 ω') ∂P))
        atTop id (fun _ => P) (μG : Measure C(↥U, Rn m)) := by sorry

end KingRockAsymp.Distribution
