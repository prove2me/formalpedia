-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrimePower_localGamma_norm_one
-- name    : OAI.SevenEighths.ProbePrimePower.localGamma_norm_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:07:02.435755+00:00
-- url     : https://prove2.me/theorems/9e1d132d-4616-4769-9682-6898988e26ac
-- title:
--   The local Gauss factor has norm one
-- statement:
--   Let $p\ne0$ be an Eisenstein integer generating a maximal ideal that does not contain `goodLambda` and whose residue field has characteristic $\ne2$, and let $r\in\mathbb N$ with $0<r<6$. Then `localGamma p hp hg r` has norm $1$.
--
--   Lean: `OAI.SevenEighths.ProbePrimePower.localGamma_norm_one` in `lean/OAI/NumberTheory/DirichletL/Detector/PrimeConstants.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

lemma localGamma_norm_one (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) : ‖localGamma p hp hg r‖ = 1 := by
  sorry

end SevenEighths.ProbePrimePower
end

end OAI
end
