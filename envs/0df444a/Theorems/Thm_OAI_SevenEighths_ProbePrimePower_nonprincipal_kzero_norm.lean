-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrimePower_nonprincipal_kzero_norm
-- name    : OAI.SevenEighths.ProbePrimePower.nonprincipal_kzero_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:52.54813+00:00
-- url     : https://prove2.me/theorems/3ab91dd9-5615-4d70-b178-793084eee713
-- title:
--   Norm of the positive scalar for k = 0 and n < 5
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda`, and $N=N((p))$. For $n<5$ and every $j$, the norm of `positiveScalar p _ (actualSextic (Ideal.span {p}) hg) n 0 j` is at most $N^n\sqrt N$.
--
--   Lean: `OAI.SevenEighths.ProbePrimePower.nonprincipal_kzero_norm` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsSharpScalar.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
lemma nonprincipal_kzero_norm (n j : ℕ) (hn : n<5) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n 0 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^n*Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  sorry

end SevenEighths.ProbePrimePower
end

end OAI
end
