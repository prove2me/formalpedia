-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrimePower_even_base_kzero_norm
-- name    : OAI.SevenEighths.ProbePrimePower.even_base_kzero_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:38.151339+00:00
-- url     : https://prove2.me/theorems/df5c7a16-58a4-4a17-bfe2-0fa712fbe250
-- title:
--   Norm of the positive scalar at exponent five, k = 0
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda`, and $N=N((p))$. For all $m\in\mathbb N$ and $j<6$, the norm of `positiveScalar p _ (actualSextic (Ideal.span {p}) hg) 5 0 (j+6m)` is at most $N^5$ if $m=0$ and at most $N^6$ otherwise.
--
--   Lean: `OAI.SevenEighths.ProbePrimePower.even_base_kzero_norm` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsSharpScalar.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
lemma even_base_kzero_norm (m j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 5 0 (j+6*m)‖≤
      if m=0 then (Ideal.absNorm (Ideal.span {p}):ℝ)^5 else (Ideal.absNorm (Ideal.span {p}):ℝ)^6 := by
  sorry

end SevenEighths.ProbePrimePower
end

end OAI
end
