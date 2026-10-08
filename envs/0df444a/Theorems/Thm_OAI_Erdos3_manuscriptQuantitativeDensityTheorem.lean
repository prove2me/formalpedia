-- Prove2me | Theorems.Thm_OAI_Erdos3_manuscriptQuantitativeDensityTheorem
-- name    : OAI.Erdos3.manuscriptQuantitativeDensityTheorem
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T08:51:33.851702+00:00
-- url     : https://prove2.me/theorems/779e9cb4-1a2a-44b6-b078-6fb5268f7fb7
-- title:
--   Quasipolynomial density bound for progression-free sets (OpenAI, Theorem 1.1)
-- statement:
--   For every integer $k\ge 3$ there are real constants $C>0$, $c>0$, $\eta>0$ such that for every natural number $N\ge 3$
--
--   $$r_k(N)\le C\,N\,\exp\!\big(-c\,(\log\log N)^{1+\eta}\big),$$
--
--   where $r_k(N)$ is `extremalNumber k N`: the largest cardinality of a finite set $S\subseteq\{1,\dots,N\}$ that contains no $k$-term arithmetic progression $a,a+d,\dots,a+(k-1)d$ with $d>0$ (`APFree S k`, the negation of `HasAP S k`). In Lean the statement is the proposition `QuantitativeDensityTheorem`, which says `QuantitativeDensityBound k` for every $k\ge 3$; logarithms are `Real.log`, natural.
--
--   This is the form of OpenAI's Theorem 1.1 recorded in OpenAI's Lean; the paper states the bound as $r_k(N)\le C_kN\exp(-c_k(\log N)^{\varepsilon_k})$, and the Lean statement's $(\log\log N)^{1+\eta}$ form is the one the Lean development proves.
--
--   Lean: `OAI.Erdos3.manuscriptQuantitativeDensityTheorem` in `lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean` (OpenAI); the definitions are in the bundle `OAIErdos3B000` of this split (OpenAI's `Model.lean`). Source: OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean#L35

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B000

namespace OAI

section

namespace Erdos3

theorem manuscriptQuantitativeDensityTheorem : QuantitativeDensityTheorem := by
  sorry

end Erdos3
end
end OAI
