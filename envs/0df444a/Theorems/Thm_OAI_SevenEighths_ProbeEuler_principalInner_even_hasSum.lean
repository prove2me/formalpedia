-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_principalInner_even_hasSum
-- name    : OAI.SevenEighths.ProbeEuler.principalInner_even_hasSum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:50:03.350997+00:00
-- url     : https://prove2.me/theorems/33e0448a-a340-4599-b0fd-072e0fea3144
-- title:
--   Sum of the principal inner Euler series
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda`, $N=N((p))$, and $\eta,a,X,W,V\in\mathbb C$ with $|V|<1$ and $|R|<1$ for $R=$`evenRatio N a X V`. Then the series $l\mapsto$`principalInner p hp hg η a X W V 0 l` has sum
--   $$\frac{R(1-N^{-1})/(1-V)+WR}{1-R}.$$
--
--   Lean: `OAI.SevenEighths.ProbeEuler.principalInner_even_hasSum` in `lean/OAI/NumberTheory/DirichletL/Detector/LocalSummation.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

lemma principalInner_even_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 0 l)
      ((evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  sorry

end SevenEighths.ProbeEuler
end

end OAI
end
