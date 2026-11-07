-- Prove2me | Theorems.Thm_LCAntiConc_theorem_4_10
-- name    : LCAntiConc.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:42.077255+00:00
-- url     : https://prove2.me/theorems/da990478-38e0-4b8d-9730-4faa0c831fd9
-- title:
--   Theorem 4.10 — certificates for isotropic $\kappa$-strongly log-concave laws at degree $O(\kappa^{-1}\delta^{-2}+\delta^{-30})$
-- statement:
--   There are absolute constants $\delta_0,C>0$ such that for every $0<\delta<\delta_0$ and every $0<\kappa\le1$ there is an even polynomial $q=q_{\delta,\kappa}$ of degree $m\le C\kappa^{-1}\delta^{-2}$ with $q\ge0$ on $\mathbb R$ and $q(t)\ge1$ for $|t|\le\delta$, whose coefficients satisfy $\sum_{k=0}^m|b_k|\le m^{Cm}$, and a degree $D\le C(\kappa^{-1}\delta^{-2}+\delta^{-30})$, such that every isotropic $\kappa$-strongly log-concave $X\in\mathbb R^d$, in every dimension $d$, satisfies
--
--   $$\{\|v\|^2=1\}\vdash_D\ \mathop{\mathbb E}_X q(\langle X,v\rangle)\le C\delta .$$
--
--   Differences from the source:
--   - reading: "δ smaller than a small enough absolute constant" → ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀); reason: the usual meaning of the phrase
--   - reading: each O(·) (m ≤ O(κ⁻¹δ⁻²), D = O(κ⁻¹δ⁻² + δ⁻³⁰), the O(δ) bound and m^{O(m)}) → one universal constant C, quantified first; reason: p.27: the constants hidden in the O(·) notation are universal; one constant for several O's is equivalent (take the maximum)
--   - reading: "q depends only on δ (and κ), but neither on the dimension d nor on the distribution of X" (p.27), and the D of the display → q and D chosen after δ and κ and before d and the law; reason: p.27 states it; D is a function of κ and δ only
--   - encoding: random vector X ∈ ℝ^d → its law μ, a probability measure on EuclideanSpace ℝ (Fin d); reason: Euclidean norm and inner product; same instances
--   - encoding: density e^{-V}, V : ℝ^d → ℝ ∪ {+∞} convex → density f = e^{-V} ≥ 0 with f((1-θ)x+θy) ≥ f(x)^{1-θ} f(y)^θ (resp. for f(x)e^{κ‖x‖²/2}); reason: convexity of V = -log f with values in ℝ ∪ {+∞}; same class
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Theorem 4.10, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_LCAntiConc_IsIsotropic
import Definitions.Def_LCAntiConc_IsStronglyLogConcave
import Definitions.Def_LCAntiConc_SphereSoSLe
import Definitions.Def_LCAntiConc_expectQ

namespace LCAntiConc

open MeasureTheory

/-- **Theorem 4.10** (Certificates for Strongly Log-Concave Distributions). Let `0 < δ` be smaller
than a small enough absolute constant and `0 < κ ≤ 1`. There is an even polynomial `q = q_{δ,κ}` of
degree `m ≤ O(κ⁻¹δ⁻²)` satisfying `q ≥ 0` and `q(t) ≥ 1` for `|t| ≤ δ`, such that every isotropic
`κ`-strongly log-concave `X ∈ ℝ^d` satisfies `{‖v‖² = 1} ⊢_D 𝔼_X q(⟨X, v⟩) ≤ O(δ)`, where
`D = O(κ⁻¹δ⁻² + δ⁻³⁰)`. Moreover `∑_{k=0}^m |b_k| ≤ m^{O(m)}` for `q(t) = ∑_{k=0}^m b_k t^k`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Theorem 4.10, p.27 (PDF p.29).

**Formalization Note** One universal constant `C` serves every `O(·)`; it and `δ₀` come before
`δ` and `κ`. `q` and `D` depend only on `δ` and `κ`, and come before `d` and the law. `m` is
`q.natDegree`. -/
theorem theorem_4_10 :
    ∃ δ₀ > 0, ∃ C > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      ∃ q : Polynomial ℝ, (∀ t, q.eval (-t) = q.eval t) ∧ (∀ t, 0 ≤ q.eval t) ∧
        (∀ t, |t| ≤ δ → 1 ≤ q.eval t) ∧ (q.natDegree : ℝ) ≤ C * κ⁻¹ * δ ^ (-2 : ℤ) ∧
        ∑ k ∈ Finset.range (q.natDegree + 1), |q.coeff k| ≤
          (q.natDegree : ℝ) ^ (C * q.natDegree) ∧
        ∃ D : ℕ, (D : ℝ) ≤ C * (κ⁻¹ * δ ^ (-2 : ℤ) + δ ^ (-30 : ℤ)) ∧
          ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))),
            IsIsotropic μ → IsStronglyLogConcave κ μ → SphereSoSLe D (expectQ μ q) (C * δ) := by sorry

end LCAntiConc
