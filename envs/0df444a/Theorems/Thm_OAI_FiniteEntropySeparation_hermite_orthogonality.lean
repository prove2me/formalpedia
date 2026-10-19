-- Prove2me | Theorems.Thm_OAI_FiniteEntropySeparation_hermite_orthogonality
-- name    : OAI.FiniteEntropySeparation.hermite_orthogonality
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:05:25.212984+00:00
-- url     : https://prove2.me/theorems/21d10498-62e9-45d5-88d8-61c1d84b1fd7
-- title:
--   Orthogonality of the probabilists' Hermite polynomials: E[Heₙ(Z)Heₘ(Z)] = n!·δₙₘ for a standard Gaussian Z
-- statement:
--   For $n \in \mathbb N$ let $\mathrm{He}_n$ be the $n$-th probabilists' Hermite polynomial, Mathlib's `Polynomial.hermite n` (an integer polynomial, with $\mathrm{He}_{n+1} = X\,\mathrm{He}_n - \mathrm{He}_n'$ and $\mathrm{He}_0 = 1$), mapped to a real polynomial by `Polynomial.map (Int.castRingHom ℝ)`. Let $\gamma$ be the standard Gaussian measure on $\mathbb R$ (`gaussianReal 0 1`). Then for all $n, m \in \mathbb N$,
--   $$\int \mathrm{He}_n(x)\,\mathrm{He}_m(x)\,d\gamma(x) \;=\; \begin{cases} n! & n = m,\\ 0 & n \ne m,\end{cases}$$
--   where the integrand is the evaluation at $x$ of the product polynomial (`(… * …).eval x`).
--
--   Lean: `OAI.FiniteEntropySeparation.hermite_orthogonality`. It uses only Mathlib. OpenAI's theorem `realHermite_inner` states `gaussianPolyIntegral (realHermite n * realHermite m) = if n = m then n! else 0`, with `realHermite n = (Polynomial.hermite n).map (Int.castRingHom ℝ)` and `gaussianPolyIntegral P = ∫ x, P.eval x ∂gaussianReal 0 1`; this statement unfolds those definitions.
-- source:
--   Classical (C. Hermite, Sur un nouveau développement en série des fonctions, Comptes Rendus de l'Académie des Sciences 58 (1864)). Proof: OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeEntropy/GaussianHermite.lean (OpenAI's theorem OAI.FiniteEntropySeparation.realHermite_inner, restated with its definitions unfolded)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
 theorem hermite_orthogonality (n m : ℕ) :
    (∫ x, (((Polynomial.hermite n).map (Int.castRingHom ℝ)) *
        ((Polynomial.hermite m).map (Int.castRingHom ℝ))).eval x ∂gaussianReal 0 1) =
      if n = m then (n.factorial : ℝ) else 0 := by
  sorry
end FiniteEntropySeparation

end

end OAI
end
