-- Prove2me | Theorems.Thm_MassartDKW_Tight_theorem_1
-- name    : MassartDKW.Tight.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:57:47.540874+00:00
-- url     : https://prove2.me/theorems/03931606-bbf7-4e75-9e0e-5802c2fb2bc6
-- title:
--   Theorem 1 (1.4), p. 1270 — P(Dₙ⁻ > λ) ≤ exp(−2λ²) for λ ≥ √(log 2/2) ∧ 1.0841 n^{−1/6}
-- statement:
--   Let $n\ge1$ and let $x_1,\dots,x_n$ be independent, identically distributed real random variables with continuous distribution function $F$. Let $\hat F_n$ be their empirical distribution function and $D_n^-=\sqrt n\sup_{x\in\mathbb R}\bigl(F(x)-\hat F_n(x)\bigr)$. Let $\gamma=1.0841$. For every $\lambda$ with
--   $$\lambda\ \ge\ \sqrt{\log(2)/2}\ \wedge\ \gamma n^{-1/6},$$
--   one has
--   $$P(D_n^->\lambda)\le\exp(-2\lambda^2).$$
--
--   This is the Dvoretzky–Kiefer–Wolfowitz inequality with the constant $1$ conjectured by Birnbaum and McCarty (1958), under a mild lower bound on $\lambda$. Since $D_n^-$ and $D_n^+$ have the same law, the same bound holds for $P(\sqrt n\sup_x(\hat F_n-F)>\lambda)$.
--
--   **Formalization Note** $\wedge$ is the minimum, so the hypothesis is that $\lambda$ is at least the smaller of $\sqrt{\log 2/2}$ and $\gamma n^{-1/6}$. "Any integer $n$" is read as $n\ge1$. The sample is `X : Fin n → Ω → ℝ`, independent (`iIndepFun`) with common law $\mu$ (`HasLaw (X i) μ P`), and $F$ is `cdf μ`, assumed continuous. The probability of the event $\{D_n^->\lambda\}$ is a value in $[0,\infty]$ and is compared with `ENNReal.ofReal` of $\exp(-2\lambda^2)$. Each supremum in $D_n^-$ is of a function with values in $[-1,1]$, hence a genuine supremum. `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1270, Theorem 1, (1.4)

import Mathlib
import Definitions.Def_MassartDKW_Tight_EmpiricalProcess
open MeasureTheory ProbabilityTheory

namespace MassartDKW.Tight

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hF : Continuous (cdf μ)) (X : Fin n → Ω → ℝ) (hlaw : ∀ i, HasLaw (X i) μ P)
    (hind : iIndepFun X P)
    (l : ℝ) (hl : min (Real.sqrt (Real.log 2 / 2)) (1.0841 * (n : ℝ) ^ (-(1 / 6 : ℝ))) ≤ l) :
    P {ω | l < Dminus μ X ω} ≤ ENNReal.ofReal (Real.exp (-2 * l ^ 2)) := by sorry

end MassartDKW.Tight
