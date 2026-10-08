-- Prove2me | Theorems.Thm_MassartDKW_Tight_smirnov_exact
-- name    : MassartDKW.Tight.smirnov_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:29.881445+00:00
-- url     : https://prove2.me/theorems/582e2bc5-4fd1-4e6f-bd58-f07d9e66882b
-- title:
--   (2.3) from (2.1), pp. 1271–1272 — Smirnov's exact law P(Dₙ⁻ > λ) = Σ_{0≤j<n−λ√n} p_{λ,n}(j)
-- statement:
--   Let $n\ge1$ and let $x_1,\dots,x_n$ be i.i.d. real random variables with continuous distribution function $F$. For $0<\lambda<\sqrt n$,
--   $$P(D_n^->\lambda)=\sum_{0\le j<n-\lambda\sqrt n}p_{\lambda,n}(j),\qquad p_{\lambda,n}(j)=\lambda\sqrt n\,(j+\lambda\sqrt n)^{j-1}(n-j-\lambda\sqrt n)^{n-j}n^{-n}\binom nj .$$
--
--   This is Smirnov's (1944) exact formula for the one-sided Kolmogorov–Smirnov statistic, (2.3) of the paper, obtained by summing the point probabilities (2.1) of the first time $-Z_n$ crosses the level $\lambda$. The paper cites it and does not prove it; every later step of the proof of Theorem 1 works with this sum.
--
--   **Formalization Note** The range printed under (2.1) reads "$0\le j<\lambda\sqrt n$"; this is a slip for $0\le j<n-\lambda\sqrt n$, the range of (2.3) and of Proposition 1, which is the range used here. The case $\lambda\ge\sqrt n$, where $P(D_n^->\lambda)=0$, is excluded as on p. 1271. `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), pp. 1271–1272, (2.1) and (2.3) (due to Smirnov 1944)

import Mathlib
import Definitions.Def_MassartDKW_Tight_EmpiricalProcess
import Definitions.Def_MassartDKW_Tight_Analytic
open MeasureTheory ProbabilityTheory

namespace MassartDKW.Tight

theorem smirnov_exact {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hF : Continuous (cdf μ)) (X : Fin n → Ω → ℝ) (hlaw : ∀ i, HasLaw (X i) μ P)
    (hind : iIndepFun X P)
    (l : ℝ) (hl0 : 0 < l) (hl : l < Real.sqrt n) :
    P {ω | l < Dminus μ X ω} = ENNReal.ofReal (smirnovTail n l) := by sorry

end MassartDKW.Tight
