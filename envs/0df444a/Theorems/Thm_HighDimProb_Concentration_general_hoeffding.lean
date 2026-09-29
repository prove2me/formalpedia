-- Prove2me | Theorems.Thm_HighDimProb_Concentration_general_hoeffding
-- name    : HighDimProb.Concentration.general_hoeffding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:36:51.897194+00:00
-- url     : https://prove2.me/theorems/6cc0e0e3-cef2-4d53-b541-5f60c155bd4b
-- title:
--   Theorem 2.6.3 — General Hoeffding's inequality
-- statement:
--   This is the **general (sub-gaussian) Hoeffding's inequality**, extending Theorem 2.2.2
--   from Rademacher random variables to arbitrary mean-zero sub-gaussian random variables.
--
--   There exists an absolute constant $c > 0$ (not depending on the sample size, the random
--   variables, the weight vector, or the deviation level) such that the following holds. Let
--   $(\Omega, \mathcal F, P)$ be a probability space, let $N \in \mathbb N$, and let
--   $X_1, \dots, X_N : \Omega \to \mathbb R$ be independent, mean-zero, sub-gaussian random
--   variables (finite $\|X_i\|_{\psi_2}$, the Orlicz norm of the companion definition). For
--   any $a = (a_1, \dots, a_N) \in \mathbb R^N$ and any $t \ge 0$,
--
--   $$
--   P\Bigl\{\Bigl|\sum_{i=1}^N a_i X_i\Bigr| \ge t\Bigr\}
--     \;\le\; 2\exp\!\left(-\frac{ct^2}{K^2\|a\|_2^2}\right),
--   $$
--
--   where $K = \max_i \|X_i\|_{\psi_2}$ and $\|a\|_2^2 = \sum_i a_i^2$.
--
--   The proof rests on an approximate rotation-invariance property: a sum of independent
--   mean-zero sub-gaussian random variables is itself sub-gaussian, with
--   $\|\sum_i X_i\|_{\psi_2}^2 \lesssim \sum_i \|X_i\|_{\psi_2}^2$, which recovers exactly the
--   exact rotation invariance of independent Gaussians up to an absolute constant.
--
--   **Formalization Note** The sub-gaussian hypothesis on each $X_i$ is stated directly, in
--   the same convention as the `subgaussianNorm` definition: $\exists\, s>0$ with
--   $\mathbb E\exp(X_i^2/s^2)\le 2$. The absolute constant $c$ is existentially quantified
--   ahead of every other object in the statement (the probability space, $N$, the $X_i$, $a$,
--   and $t$), so no numeral is fixed for it — a solver's proof may establish it with any
--   positive value. $K = \max_i \|X_i\|_{\psi_2}$ is Mathlib's `iSup` over `Fin N` (which, for
--   $N=0$, defaults to the junk value $0$; the statement is then trivial since the sum and
--   $\|a\|_2$ are also $0$).
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 2.6.3, p. 30 (PDF p. 38)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm

open MeasureTheory ProbabilityTheory Real

namespace HighDimProb.Concentration

/-- **Theorem 2.6.3** (General Hoeffding's inequality), Vershynin, *High-Dimensional
Probability* (2018), p. 30.

Let `X₁, …, X_N` be independent, mean zero, sub-gaussian random variables, and
`a = (a₁, …, a_N) ∈ ℝᴺ`. Then, for every `t ≥ 0`,

`P {|∑ᵢ aᵢXᵢ| ≥ t} ≤ 2 exp(−ct² / (K²‖a‖₂²))`, where `K = maxᵢ ‖Xᵢ‖_{ψ₂}` and `c > 0` is an
absolute constant (not depending on `N`, the `Xᵢ`, `a`, or `t`). -/
theorem general_hoeffding :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N : ℕ} (X : Fin N → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X P →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, ∃ s > 0, Integrable (fun ω => Real.exp ((X i ω) ^ 2 / s ^ 2)) P ∧
                       ∫ ω, Real.exp ((X i ω) ^ 2 / s ^ 2) ∂P ≤ 2) →
        ∀ (a : Fin N → ℝ) {t : ℝ}, 0 ≤ t →
        P.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
          2 * Real.exp (-(c * t ^ 2 /
            ((⨆ i, subgaussianNorm P (X i)) ^ 2 * ∑ i, (a i) ^ 2))) := by sorry

end HighDimProb.Concentration
