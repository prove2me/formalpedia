-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrimePower_actualSextic_neg_one_sq
-- name    : OAI.SevenEighths.ProbePrimePower.actualSextic_neg_one_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T00:23:44.594387+00:00
-- url     : https://prove2.me/theorems/96f48138-a3ac-43a1-b276-d5326fc93061
-- title:
--   The sextic character squares to one at minus one
-- statement:
--   For every maximal ideal $P$ of $\mathcal O$ (`ActualEisensteinCubic.O`) not containing `goodLambda` (witness `hg`), the sextic residue character $\chi=\texttt{actualSextic}\,P\,\texttt{hg}$ satisfies $\chi(-1)^2=1$.
--
--   Lean: `OAI.SevenEighths.ProbePrimePower.actualSextic_neg_one_sq` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B008

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma actualSextic_neg_one_sq (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) : actualSextic P hg (-1)^2 = 1 := by
  sorry

end SevenEighths.ProbePrimePower
end

end OAI
end
