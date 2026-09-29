-- Prove2me | Theorems.Thm_HighDimProb_Concentration_bernstein_weighted
-- name    : HighDimProb.Concentration.bernstein_weighted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:37:58.722158+00:00
-- url     : https://prove2.me/theorems/4b30a79e-1b02-4049-bfd5-4390417053bd
-- title:
--   Theorem 2.8.2 — Bernstein's inequality (weighted sum)
-- statement:
--   This is **Bernstein's inequality** for a weighted sum of independent, mean-zero,
--   sub-exponential random variables — the goal theorem of this mission, obtained by applying
--   the unweighted Theorem 2.8.1 to the rescaled variables $a_iX_i$.
--
--   There exists an absolute constant $c > 0$ (not depending on the sample size, the random
--   variables, the weight vector, or the deviation level) such that the following holds. Let
--   $(\Omega, \mathcal F, P)$ be a probability space, let $N \in \mathbb N$, and let
--   $X_1, \dots, X_N : \Omega \to \mathbb R$ be independent, mean-zero, sub-exponential random
--   variables. For any $a = (a_1, \dots, a_N) \in \mathbb R^N$ and any $t \ge 0$,
--
--   $$
--   P\Bigl\{\Bigl|\sum_{i=1}^N a_i X_i\Bigr| \ge t\Bigr\}
--     \;\le\; 2\exp\!\left[-c\min\!\left(\frac{t^2}{K^2\|a\|_2^2}, \frac{t}{K\|a\|_\infty}\right)\right],
--   $$
--
--   where $K = \max_i \|X_i\|_{\psi_1}$, $\|a\|_2^2 = \sum_i a_i^2$, and
--   $\|a\|_\infty = \max_i |a_i|$.
--
--   This is the sharpest and most general form of concentration proved in this chapter: it
--   specializes to the unweighted Theorem 2.8.1 when $a_i \equiv 1$, and to a Bernstein bound
--   for sample averages when $a_i \equiv 1/N$. Setting $t \le c'\sqrt N$ (for a suitable
--   absolute constant $c'$) recovers a purely sub-gaussian tail, matching the shape one would
--   naively expect from the central limit theorem in the small-deviation regime; larger $t$
--   is where the sub-exponential correction becomes necessary and the bound genuinely departs
--   from a Gaussian tail.
--
--   **Formalization Note** Same conventions as `bernstein_unweighted`: the sub-exponential
--   hypothesis on each $X_i$ is $\exists\, s > 0$ with $\mathbb E\exp(|X_i|/s) \le 2$, and the
--   absolute constant $c$ is existentially quantified ahead of every other object in the
--   statement, so no numeral is fixed for it. $K = \max_i \|X_i\|_{\psi_1}$ and
--   $\|a\|_\infty = \max_i |a_i|$ are both Mathlib's `iSup` over `Fin N`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 2.8.2, p. 38 (PDF p. 46)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubexponentialNorm

open MeasureTheory ProbabilityTheory Real

namespace HighDimProb.Concentration

/-- **Theorem 2.8.2** (Bernstein's inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 38.

Let `X₁, …, X_N` be independent, mean zero, sub-exponential random variables, and
`a = (a₁, …, a_N) ∈ ℝᴺ`. Then, for every `t ≥ 0`,

`P {|∑ᵢ aᵢXᵢ| ≥ t} ≤ 2 exp[−c min(t² / (K²‖a‖₂²), t / (K‖a‖∞))]`, where `K = maxᵢ ‖Xᵢ‖_{ψ₁}`
and `c > 0` is an absolute constant (not depending on `N`, the `Xᵢ`, `a`, or `t`). -/
theorem bernstein_weighted :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N : ℕ} (X : Fin N → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X P →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, ∃ s > 0, Integrable (fun ω => Real.exp (|X i ω| / s)) P ∧
                       ∫ ω, Real.exp (|X i ω| / s) ∂P ≤ 2) →
        ∀ (a : Fin N → ℝ) {t : ℝ}, 0 ≤ t →
        P.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
          2 * Real.exp (-(c * min
            (t ^ 2 / ((⨆ i, subexponentialNorm P (X i)) ^ 2 * ∑ i, (a i) ^ 2))
            (t / ((⨆ i, subexponentialNorm P (X i)) * ⨆ i, |a i|)))) := by sorry

end HighDimProb.Concentration
