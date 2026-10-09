-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrimePower_even_base_kone_zero
-- name    : OAI.SevenEighths.ProbePrimePower.even_base_kone_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:29.437264+00:00
-- url     : https://prove2.me/theorems/5b19506f-97f4-4ba0-9c82-6bdc9a0f193e
-- title:
--   A vanishing positive scalar at exponent five
-- statement:
--   Let $p$ be a prime Eisenstein integer (`ActualEisensteinCubic.O`) generating a maximal ideal that does not contain `goodLambda` (witness `hg`). For every $j<6$, `positiveScalar p _ (actualSextic (Ideal.span {p}) hg) 5 1 j` $=0$.
--
--   Lean: `OAI.SevenEighths.ProbePrimePower.even_base_kone_zero` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsSharpScalar.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma even_base_kone_zero (j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 5 1 j=0 := by
  sorry

end SevenEighths.ProbePrimePower
end

end OAI
end
