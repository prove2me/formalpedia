-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_principalMarkedSeries_eq
-- name    : OAI.SevenEighths.ProbeEuler.principalMarkedSeries_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:17.746221+00:00
-- url     : https://prove2.me/theorems/7f4b1e32-8b82-4689-99a3-82e9c0996410
-- title:
--   Closed form of the principal marked Euler series
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda`, $N=N((p))$, and $\eta,a,X,W,V\in\mathbb C$ with $|V|<1$ and $|R|<1$ for $R=$`evenRatio N a X V`. Then `principalMarkedSeries p hp hg η a X W V` $=$ `markedFactor R V N⁻¹ (η(N-1)XW) (-ηX+WR) 1`.
--
--   Lean: `OAI.SevenEighths.ProbeEuler.principalMarkedSeries_eq` in `lean/OAI/NumberTheory/DirichletL/Detector/LocalSummation.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

include hc

theorem principalMarkedSeries_eq (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    principalMarkedSeries p hp hg eta a X W V =
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-eta*X+W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  sorry

end SevenEighths.ProbeEuler
end

end OAI
end
