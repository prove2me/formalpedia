-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_budget_limit
-- name    : HouseAllocLT.LowerBound.budget_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:19.574557+00:00
-- url     : https://prove2.me/theorems/d3026093-9948-4157-9502-9d19a8d8246a
-- title:
--   Theorem 3.1, proof, final paragraph — limit of Bₙ/n
-- statement:
--   For the harmonic budget $B_n$ defined in (6),
--
--   $$\lim_{n\to\infty}\frac{B_n}{n}=1-e^{-1}.$$
--
--   This is the asymptotic budget fraction established in the final paragraph of Theorem 3.1's proof.
--
--   Differences from the source:
--   - encoding: B_n defined for n at least two → B_0=B_1=0 and real division at zero is total; reason: a limit at infinity is unchanged by those two values
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Theorem 3.1, proof, final paragraph, PDF p. 9 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_prefixList

open scoped BigOperators ENNReal Topology
open Filter

namespace HouseAllocLT.LowerBound

/-- Theorem 3.1, proof, final paragraph, PDF p.9 (printed p.7).
B is totalized by zero below n=2; those two values do not affect this limit. -/
theorem budget_limit :
    Tendsto (fun n : ℕ => B n / (n : ℝ)) atTop (𝓝 (1 - Real.exp (-1))) := by sorry

end HouseAllocLT.LowerBound
