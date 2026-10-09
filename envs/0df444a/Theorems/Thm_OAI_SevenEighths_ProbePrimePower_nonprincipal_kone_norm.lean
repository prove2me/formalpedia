-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrimePower_nonprincipal_kone_norm
-- name    : OAI.SevenEighths.ProbePrimePower.nonprincipal_kone_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:48:50.661382+00:00
-- url     : https://prove2.me/theorems/aca4b4ba-2ac3-40f2-bdde-e79601a3b211
-- title:
--   Norm of the positive scalar for k = 1 and 0 < n < 6
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda`, and $N=N((p))$. For $0<n<6$ and every $j$, the norm of `positiveScalar p _ (actualSextic (Ideal.span {p}) hg) n 1 j` is at most $N^{n+1}$.
--
--   Lean: `OAI.SevenEighths.ProbePrimePower.nonprincipal_kone_norm` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsSharpScalar.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
lemma nonprincipal_kone_norm (n j : ℕ) (hn : 0<n) (hn6 : n<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1) := by
  sorry

end SevenEighths.ProbePrimePower
end

end OAI
end
