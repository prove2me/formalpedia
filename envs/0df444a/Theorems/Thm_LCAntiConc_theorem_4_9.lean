-- Prove2me | Theorems.Thm_LCAntiConc_theorem_4_9
-- name    : LCAntiConc.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:51.184695+00:00
-- url     : https://prove2.me/theorems/4defeddd-72b6-44e4-8d79-c91f1b38b388
-- title:
--   Theorem 4.9 — certificates for isotropic log-concave laws: one even $q_\delta$, degree $D=O(m+\delta^{-30})\le\exp(O(1/\delta))$
-- statement:
--   There are absolute constants $\delta_0,C>0$ such that for every $0<\delta<\delta_0$ there is an even polynomial $q=q_\delta$ of degree $m\le\exp(C/\delta)$ with $q\ge0$ on $\mathbb R$ and $q(t)\ge1$ for $|t|\le\delta$, whose coefficients $q(t)=\sum_{k=0}^mb_kt^k$ satisfy $\sum_{k=0}^m|b_k|\le m^{Cm}$, and a degree $D\le C(m+\delta^{-30})$ with $D\le\exp(C/\delta)$, such that every isotropic log-concave $X\in\mathbb R^d$, in every dimension $d$, satisfies
--
--   $$\{\|v\|^2=1\}\vdash_D\ \mathop{\mathbb E}_X q(\langle X,v\rangle)\le C\delta .$$
--
--   The same polynomial and the same degree work for all isotropic log-concave distributions in all dimensions.
--
--   Differences from the source:
--   - reading: "δ smaller than a small enough absolute constant" → ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀); reason: the usual meaning of the phrase
--   - reading: each O(·) (m ≤ exp(O(1/δ)), D = O(m + δ⁻³⁰) ≤ exp(O(1/δ)), the O(δ) bound and m^{O(m)}) → one universal constant C, quantified first; reason: p.27: the constants hidden in the O(·) notation are universal; one constant for several O's is equivalent (take the maximum)
--   - reading: "q depends only on δ … neither on the dimension d nor on the distribution of X" (p.27), and the D of the display → q and D chosen after δ and before d and the law; reason: p.27 states it; D is a function of m and δ only
--   - encoding: random vector X ∈ ℝ^d → its law μ, a probability measure on EuclideanSpace ℝ (Fin d); reason: Euclidean norm and inner product; same instances
--   - encoding: density e^{-V}, V : ℝ^d → ℝ ∪ {+∞} convex → density f = e^{-V} ≥ 0 with f((1-θ)x+θy) ≥ f(x)^{1-θ} f(y)^θ (resp. for f(x)e^{κ‖x‖²/2}); reason: convexity of V = -log f with values in ℝ ∪ {+∞}; same class
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Theorem 4.9, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_LCAntiConc_IsIsotropic
import Definitions.Def_LCAntiConc_IsLogConcave
import Definitions.Def_LCAntiConc_SphereSoSLe
import Definitions.Def_LCAntiConc_expectQ

namespace LCAntiConc

open MeasureTheory

/-- **Theorem 4.9** (Certificates for Log-Concave Distributions). Let `0 < δ` be smaller than a
small enough absolute constant. There is an even polynomial `q = q_δ` of degree
`m ≤ exp(O(1/δ))` satisfying `q ≥ 0` and `q(t) ≥ 1` for `|t| ≤ δ`, such that every isotropic
log-concave `X ∈ ℝ^d` satisfies `{‖v‖² = 1} ⊢_D 𝔼_X q(⟨X, v⟩) ≤ O(δ)`, where
`D = O(m + δ⁻³⁰) ≤ exp(O(1/δ))`. Moreover, writing `q(t) = ∑_{k=0}^m b_k t^k`, the coefficients of
`q` satisfy `∑_{k=0}^m |b_k| ≤ m^{O(m)}`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Theorem 4.9, p.27 (PDF p.29).

**Formalization Note** One universal constant `C` serves every `O(·)` (p.27: "the constants
hidden in the `O(·)` notation are universal"); it and `δ₀` come first. `q` and `D` depend only on
`δ`, and come before `d` and the law. `m` is `q.natDegree`. -/
theorem theorem_4_9 :
    ∃ δ₀ > 0, ∃ C > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ q : Polynomial ℝ, (∀ t, q.eval (-t) = q.eval t) ∧ (∀ t, 0 ≤ q.eval t) ∧
        (∀ t, |t| ≤ δ → 1 ≤ q.eval t) ∧ (q.natDegree : ℝ) ≤ Real.exp (C / δ) ∧
        ∑ k ∈ Finset.range (q.natDegree + 1), |q.coeff k| ≤
          (q.natDegree : ℝ) ^ (C * q.natDegree) ∧
        ∃ D : ℕ, (D : ℝ) ≤ C * (q.natDegree + δ ^ (-30 : ℤ)) ∧ (D : ℝ) ≤ Real.exp (C / δ) ∧
          ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))),
            IsIsotropic μ → IsLogConcave μ → SphereSoSLe D (expectQ μ q) (C * δ) := by sorry

end LCAntiConc
