-- Prove2me | Theorems.Thm_LCAntiConc_theorem_1_2
-- name    : LCAntiConc.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:40.580787+00:00
-- url     : https://prove2.me/theorems/88fa1a63-41d7-4459-9b8e-5833d7af321c
-- title:
--   Theorem 1.2 — dimension-independent anti-concentration certificates for isotropic (strongly) log-concave laws
-- statement:
--   There are absolute constants $\delta_0>0$ and $C>0$ such that for every $0<\delta<\delta_0$:
--
--   1. **Log-concave distributions.** For every dimension $d$, every isotropic log-concave $X\in\mathbb R^d$ is $\delta$-certifiably anti-concentrated (Definition 1.1, with constant $C$ in place of the $O(\delta)$ of (1.3)) at some degree
--
--   $$D\le C\exp(C/\delta).$$
--
--   2. **Strongly log-concave distributions.** For every $0<\kappa\le1$ and every dimension $d$, every isotropic $\kappa$-strongly log-concave $X\in\mathbb R^d$ is $\delta$-certifiably anti-concentrated, with the same constant, at some degree
--
--   $$D\le C\big(\kappa^{-1}\delta^{-2}+\delta^{-30}\big).$$
--
--   The constants do not depend on $d$, $\kappa$ or the distribution, so the certificates can be found by a semidefinite program in time $d^{O(D)}$, polynomial in $d$ for fixed $\delta$.
--
--   Differences from the source:
--   - reading: "δ smaller than a small enough absolute constant" → ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀); reason: the usual meaning of the phrase
--   - reading: each O(·) (the O(δ) of (1.3) in Definition 1.1 and the two degree bounds) → one universal constant C, quantified first; reason: p.27: the constants hidden in the O(·) notation are universal; one constant for several O's is equivalent (take the maximum)
--   - reading: "degree O(exp(O(1/δ)))" → D ≤ C exp(C/δ), the same C; reason: one constant for both O's is equivalent (take the maximum)
--   - encoding: 𝔼 q(⟨X, v⟩) in (1.3) → the certificate also asserts that the coefficients of q(⟨x, v⟩) are integrable; reason: (1.3) presupposes the polynomial exists; for isotropic log-concave laws all moments are finite
--   - encoding: random vector X ∈ ℝ^d → its law μ, a probability measure on EuclideanSpace ℝ (Fin d); reason: Euclidean norm and inner product; same instances
--   - encoding: density e^{-V}, V : ℝ^d → ℝ ∪ {+∞} convex → density f = e^{-V} ≥ 0 with f((1-θ)x+θy) ≥ f(x)^{1-θ} f(y)^θ (resp. for f(x)e^{κ‖x‖²/2}); reason: convexity of V = -log f with values in ℝ ∪ {+∞}; same class
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Theorem 1.2, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_LCAntiConc_IsIsotropic
import Definitions.Def_LCAntiConc_IsLogConcave
import Definitions.Def_LCAntiConc_IsStronglyLogConcave
import Definitions.Def_LCAntiConc_IsCertAntiConc

namespace LCAntiConc

open MeasureTheory

/-- **Theorem 1.2** (Anti-concentration certificates). Let `0 < δ` be smaller than a small enough
absolute constant and `0 < κ ≤ 1`.
1. *Log-concave distributions.* Every isotropic log-concave `X ∈ ℝ^d` is `δ`-certifiably
   anti-concentrated at degree `O(exp(O(1/δ)))`.
2. *Strongly log-concave distributions.* Every isotropic `κ`-strongly log-concave `X ∈ ℝ^d` is
   `δ`-certifiably anti-concentrated at degree `D = O(κ⁻¹δ⁻² + δ⁻³⁰)`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Theorem 1.2, p.2 (PDF p.4).

**Formalization Note** "Smaller than a small enough absolute constant" is `∃ δ₀ > 0` before `δ`.
Every `O(·)` is a universal constant (p.27), so one constant `C` serves the `O(δ)` of (1.3) and
both degree bounds; `δ₀` and `C` come before `δ`, `κ`, `d` and the law, which is what makes the
certificates dimension-independent. "Degree `O(exp(O(1/δ)))`" is `D ≤ C exp(C/δ)`. -/
theorem theorem_1_2 :
    ∃ δ₀ > 0, ∃ C > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      (∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))), IsIsotropic μ → IsLogConcave μ →
        ∃ D : ℕ, (D : ℝ) ≤ C * Real.exp (C / δ) ∧ IsCertAntiConc μ δ D C) ∧
      (∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))),
        IsIsotropic μ → IsStronglyLogConcave κ μ →
        ∃ D : ℕ, (D : ℝ) ≤ C * (κ⁻¹ * δ ^ (-2 : ℤ) + δ ^ (-30 : ℤ)) ∧
          IsCertAntiConc μ δ D C) := by sorry

end LCAntiConc
