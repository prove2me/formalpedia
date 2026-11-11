-- Prove2me | Theorems.Thm_HZFixp_Main_theorem_3_4
-- name    : HZFixp.Main.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:02.578885+00:00
-- url     : https://prove2.me/theorems/0ea0bef8-c9fd-4026-a5af-56f744f0c594
-- title:
--   Theorem 3.4 — Reciprocal VI is FIXP-hard under SL reductions
-- statement:
--   Reciprocal VI (Definition 3.3: a reciprocal graph with unary-encoded intervals $1\le a_i<b_i$ and ratios $0<\lambda_e\le a_i$, an integer $M\ge1$, disjoint designated pairs $(A_j,D_j)$ with designated ratio-one edges and intervals $[M,2M]$, $[2M,3M]$, under the promise that every solution of the box conditions (3) has $r_{A_j}+r_{D_j}=4M$; solutions $z\in[1,2]^d$ extending to a solution $r$ of (3) with $r_{A_j}=Mz_j$) is FIXP-hard:
--   $$\forall P\in\mathrm{FIXP}:\quad P\le_{SL}\text{Reciprocal VI}.$$
--
--   It is the middle reduction; the unary encoding is essential, because the market of Theorem 3.6 has size polynomial in the input numbers themselves.
--
--   Differences from the source:
--   - generalization: FIXP: reducible to a fixed point of a circuit self-map of a cube (Definition 2.4) → InFIXP via the published basicFIXP, whose domain is any nonempty bounded rational polytope; reason: a cube is such a polytope, so the Lean class contains the paper's class and hardness for it implies hardness for the paper's class
--   - encoding: polynomial time (in the binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime over fixed injective encodings into the alphabet Sym (published FixpReciprocal_SLReduces); reason: the paper names no machine model; the reused FIXP framework fixes this one
--   - encoding: unary endpoints, ratios and M; edges listed explicitly → encRVIData: every number unary (framed runs of ones), node indices unary, list lengths binary; reason: the list lengths are bounded by the written lists, so encoding lengths change by at most a polynomial
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 7 (PDF 9), Theorem 3.4; proof pp. 21–22 (PDF 23–24)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_HZFixp_Main_ReciprocalVI

open FixpReciprocal

namespace HZFixp.Main

/-- **Theorem 3.4.** Reciprocal VI is FIXP-hard under SL reductions. -/
theorem theorem_3_4 : FIXPHard rviProblem := by sorry

end HZFixp.Main
