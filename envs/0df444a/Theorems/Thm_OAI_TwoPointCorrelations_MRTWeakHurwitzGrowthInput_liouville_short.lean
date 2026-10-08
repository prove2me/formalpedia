-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_liouville_short
-- name    : OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.liouville_short
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:59.903886+00:00
-- url     : https://prove2.me/theorems/0fd572aa-0575-4493-b8bf-a86df949f022
-- title:
--   The Liouville short-interval input from the weak Hurwitz growth input and the sparse prime input
-- statement:
--   If `MRTWeakHurwitzGrowthInput` and `HalaszPrimeSparseInput` hold, then `MRTLiouvilleShortInput` holds.
--
--   `MRTWeakHurwitzGrowthInput`: there are $C,T>0$ such that for $|t|\ge T$, $a\in[0,1]$ and $s$ with $1-r(t)\le\operatorname{Re}s\le1+5r(t)$ and $|\operatorname{Im}s-t|\le3r(t)$, where $r(t)=\log(|t|+3)^{-2/3}$, one has $|\zeta(s,a)-a^{-s}\mathbf 1_{a\ne0}|\le\log(|t|+3)^C$. `MRTLiouvilleShortInput`: there is $C>0$ with $\int_0^X|\sum_{y<n\le y+H}\lambda(n)e(n\alpha)|dy\le CHX(\frac{\log\log H}{\log H}+(\log X)^{-1/700})$ for all $10\le H\le X$ and real $\alpha$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.liouville_short`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations


theorem MRTWeakHurwitzGrowthInput.liouville_short (h : MRTWeakHurwitzGrowthInput)
    (hprime : HalaszPrimeSparseInput) : MRTLiouvilleShortInput := by
  sorry

end OAI.TwoPointCorrelations
