-- Prove2me | Theorems.Thm_HighDimProb_QuadraticForms_hanson_wright
-- name    : HighDimProb.QuadraticForms.hanson_wright
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:30:45.579251+00:00
-- url     : https://prove2.me/theorems/03b09435-ba2e-4535-a470-309ed8ec161e
-- title:
--   Theorem 6.2.1 — Hanson-Wright inequality
-- statement:
--   This is the **Hanson-Wright inequality**, the capstone result of Chapter 6 of
--   Vershynin's *High-Dimensional Probability*: a concentration inequality for a quadratic
--   form ("chaos") in independent sub-gaussian random variables, playing the role for chaoses
--   that Bernstein's inequality (Chapter 2) plays for linear sums.
--
--   Let $X = (X_1, \dots, X_n) \in \mathbb R^n$ be a random vector with independent, mean
--   zero, sub-gaussian coordinates, and let $K = \max_i \|X_i\|_{\psi_2}$ be the largest of
--   their sub-gaussian (Orlicz $\psi_2$) norms. Let $A$ be an $n \times n$ matrix — with no
--   constraint on its diagonal. Then, for every $t \ge 0$,
--
--   $$
--   P\bigl\{\,|X^\top A X - \mathbb E\, X^\top A X| \ge t \,\bigr\}
--   \;\le\; 2 \exp\!\left[-c \min\!\left(\frac{t^2}{K^4 \|A\|_F^2},\ \frac{t}{K^2 \|A\|}\right)\right],
--   $$
--
--   where $\|A\|_F$ is the Frobenius norm and $\|A\|$ the operator norm of $A$, and $c > 0$
--   is an absolute constant, not depending on $n$, $X$, $A$, or $t$.
--
--   The bound has the familiar two-regime shape of Bernstein's inequality: sub-gaussian
--   (quadratic exponent) for small $t$, and sub-exponential (linear exponent) for large $t$,
--   reflecting that a quadratic form in sub-gaussian variables behaves like a sub-exponential,
--   not sub-gaussian, random variable. Unlike the Decoupling theorem's diagonal-free
--   hypothesis, $A$ here is a *general* matrix: its diagonal contributes to $\mathbb E\,
--   X^\top A X = \operatorname{tr}(A) \cdot (\text{a common second moment when the } X_i
--   \text{ are i.i.d.})$ (more precisely $\sum_i A_{ii}\, \mathbb E X_i^2$ in general) and is
--   handled by Bernstein's inequality directly in the proof, while the off-diagonal part is
--   handled by decoupling; keeping $A$ general is what makes this the actual content of the
--   chapter, rather than a restatement of Bernstein's inequality for the special case of
--   diagonal $A$.
--
--   **Formalization Note** $K = \max_i \|X_i\|_{\psi_2}$ is written directly as $\sup_i
--   \|X_i\|_{\psi_2}$ (`⨆ i, HighDimProb.Concentration.subgaussianNorm P (X i)`, reusing this
--   series' published sub-gaussian norm), and $c$ is existentially quantified *before* $n$,
--   $\Omega$, $P$, $X$, and $A$, so it cannot depend on any of them, matching the book's
--   "absolute constant". Each coordinate's sub-gaussianity is stated as membership in the
--   admissible set of the sub-gaussian norm's own definition (some finite $s > 0$ with the
--   exponential moment integrable and at most $2$), the same idiom used for the
--   sub-exponential hypothesis in this series' Bernstein's inequality. The quadratic form
--   $X^\top A X$ itself is required `Integrable`, so that $\mathbb E\, X^\top A X$ is a
--   genuine expectation and not Mathlib's junk value $0$ for a non-integrable integrand — a
--   fact that in principle follows from sub-gaussianity of the $X_i$ but is not itself proved
--   by this draft (`:= by sorry`). $\|A\|_F$ and $\|A\|$ are this mission's own
--   `frobeniusNorm` and `opNorm`. No hypothesis is imposed on $A$'s diagonal: the general
--   matrix case is the chapter's actual content, and restricting to diagonal-free $A$ would
--   collapse the statement to a restatement of Bernstein's inequality.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 6.2.1, p. 139 (PDF p. 147)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm
import Definitions.Def_HighDimProb_QuadraticForms_FrobeniusNorm
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm

open MeasureTheory ProbabilityTheory

namespace HighDimProb.QuadraticForms

/-- **Theorem 6.2.1** (Hanson-Wright inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 139.

Let `X = (X₁, …, Xₙ) ∈ ℝⁿ` be a random vector with independent, mean zero, sub-gaussian
coordinates. Let `A` be an `n × n` matrix. Then, for every `t ≥ 0`,

`P{|XᵀAX − E XᵀAX| ≥ t} ≤ 2 exp[−c min(t²/(K⁴‖A‖_F²), t/(K²‖A‖))]`,

where `K = maxᵢ ‖Xᵢ‖_{ψ₂}` and `c > 0` is an absolute constant (not depending on `n`, `X`, `A`,
or `t`). -/
theorem hanson_wright :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin n → Ω → ℝ),
        (∀ i, Measurable (X i)) →
        iIndepFun X P →
        (∀ i, Integrable (X i) P) →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, ∃ s > 0, Integrable (fun ω => Real.exp ((X i ω) ^ 2 / s ^ 2)) P ∧
                       ∫ ω, Real.exp ((X i ω) ^ 2 / s ^ 2) ∂P ≤ 2) →
        ∀ (A : Matrix (Fin n) (Fin n) ℝ),
        Integrable (fun ω => ∑ i, ∑ j, A i j * X i ω * X j ω) P →
        ∀ {t : ℝ}, 0 ≤ t →
        P.real {ω | t ≤ |∑ i, ∑ j, A i j * X i ω * X j ω -
                          ∫ ω, ∑ i, ∑ j, A i j * X i ω * X j ω ∂P|} ≤
          2 * Real.exp (-(c * min
            (t ^ 2 / ((⨆ i, HighDimProb.Concentration.subgaussianNorm P (X i)) ^ 4 *
                       frobeniusNorm A ^ 2))
            (t / ((⨆ i, HighDimProb.Concentration.subgaussianNorm P (X i)) ^ 2 *
                   opNorm A)))) := by sorry

end HighDimProb.QuadraticForms
