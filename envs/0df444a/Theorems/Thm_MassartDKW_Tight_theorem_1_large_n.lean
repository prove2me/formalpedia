-- Prove2me | Theorems.Thm_MassartDKW_Tight_theorem_1_large_n
-- name    : MassartDKW.Tight.theorem_1_large_n
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:57:25.617982+00:00
-- url     : https://prove2.me/theorems/7698a466-cd84-420b-a28a-2665a23398f4
-- title:
--   Proof of Theorem 1, pp. 1279–1280 — P(Dₙ⁻ > λ) ≤ exp(−2λ²) for n ≥ 39 and γn^{−1/6} ≤ λ ≤ √n/2
-- statement:
--   Let $n\ge39$ and let $x_1,\dots,x_n$ be i.i.d. real random variables with continuous distribution function $F$. For every $\lambda$ with $\gamma n^{-1/6}\le\lambda\le\sqrt n/2$, where $\gamma=1.0841$,
--   $$P(D_n^->\lambda)\le\exp(-2\lambda^2).$$
--
--   This is the first of the two cases of the proof of Theorem 1; for $n\ge39$ the condition of Theorem 1 reduces to $\lambda\ge\gamma n^{-1/6}$. The other case ($n\le38$ or $\lambda>\sqrt n/2$) is handled through Proposition 2 and the numerical check (2.15).
--
--   **Formalization Note** The sample is `X : Fin n → Ω → ℝ`, independent (`iIndepFun`) with common law $\mu$ (`HasLaw`) whose `cdf` is continuous. The probability is the measure of the event $\{D_n^->\lambda\}$ in $[0,\infty]$, compared with $\exp(-2\lambda^2)$. `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), pp. 1279–1280, Proof of Theorem 1 (where n ≥ 39 and λ ≤ √n/2)

import Mathlib
import Definitions.Def_MassartDKW_Tight_EmpiricalProcess
open MeasureTheory ProbabilityTheory

namespace MassartDKW.Tight

theorem theorem_1_large_n {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hF : Continuous (cdf μ)) (X : Fin n → Ω → ℝ) (hlaw : ∀ i, HasLaw (X i) μ P)
    (hind : iIndepFun X P)
    (hn39 : 39 ≤ n) (l : ℝ) (hl1 : 1.0841 * (n : ℝ) ^ (-(1 / 6 : ℝ)) ≤ l)
    (hl2 : l ≤ Real.sqrt n / 2) :
    P {ω | l < Dminus μ X ω} ≤ ENNReal.ofReal (Real.exp (-2 * l ^ 2)) := by sorry

end MassartDKW.Tight
