-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicSieve_cubic_smoothed_frequency_recurrence_all
-- name    : OAI.SevenEighths.CubicSieve.cubic_smoothed_frequency_recurrence_all
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:00:16.838739+00:00
-- url     : https://prove2.me/theorems/6ab0b064-0f06-4186-ae9e-6258b29a0abc
-- title:
--   Smoothed cubic coprime sum bounded by its frequency series
-- statement:
--   For every Schwartz function $W$ there is $C\ge0$ such that for every finite index type $n$, every $\varepsilon>0$, $M>0$, $N\ge1$, every injective `cols : n → Ideal O` (Eisenstein integers) of `Admissible` ideals with absolute norm in $[N/2,N]$ and every $a:n\to\mathbb C$,
--   $$\|\texttt{cubicSmoothedCoprime}\ \mathrm{cols}\,a\,W\,M\|\le M\Big(\tfrac2N\sum_j|a_j|^2\,\|\widehat W_{\mathrm{rad}}(0)\|+C\,S_\varepsilon N^{\varepsilon}\,\tfrac2N\sum_j|a_j|^2\sum_{l\ge0}\texttt{frequencyMajorant}\,M\,N\,l\Big),$$
--   where $\widehat W_{\mathrm{rad}}$ is `paperRadialFourier W` and $S_\varepsilon$ is `IdealCoprimeSieveOperator.supportConstant ε`.
--
--   Lean: `OAI.SevenEighths.CubicSieve.cubic_smoothed_frequency_recurrence_all` in `lean/OAI/NumberTheory/DirichletL/CubicSieve/Recurrence.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B008

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_smoothed_frequency_recurrence_all (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (((2 / N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ + C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  sorry

end
end SevenEighths.CubicSieve

end OAI
end
