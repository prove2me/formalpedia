-- Prove2me | Theorems.Thm_MarkovChainCLT_phiMixingCoef_nonneg
-- name    : MarkovChainCLT.phiMixingCoef_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:17:17.829048+00:00
-- url     : https://prove2.me/theorems/063d9571-f847-40e3-95c7-d06e3c22d355
-- title:
--   $\varphi(n)\ge 0$
-- statement:
--   The uniform mixing coefficient is nonnegative.
--
--   Let $Y_0,Y_1,\dots$ be random variables on a probability space $(\Omega,\mathcal F,P)$ and $n\ge 0$. With $\varphi(n)$ the supremum over $k$, $A\in\sigma(Y_0,\dots,Y_k)$ with $P(A)\neq 0$ and $B\in\sigma(Y_{k+n},\dots)$ of $|P(B\mid A)-P(B)|$, we have
--
--   $$
--   0\le\varphi(n).
--   $$
--
--   Indeed $0$ is attained at $A=B=\Omega$, and every element lies in $[0,1]$, so the supremum dominates it.
--
--   **Formalization Note** Lean encodes $\varphi(n)$ as a real supremum; conditional probability is $(P(A\cap B)).toReal/(P(A)).toReal$.
-- source:
--   Galin L. Jones, On the Markov chain central limit theorem, Probability Surveys 1 (2004) 299-320, Sec 3 Definition 3

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.phiMixingCoef_nonneg {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) : 0 ≤ phiMixingCoef P Y n := by sorry
