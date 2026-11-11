-- Prove2me | Theorems.Thm_HZFixp_Main_theorem_3_2
-- name    : HZFixp.Main.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:52:57.422262+00:00
-- url     : https://prove2.me/theorems/3cbd9d23-787f-4b7d-9aed-440213369594
-- title:
--   Theorem 3.2 — Quadratic Fixed Point is FIXP-hard under SL reductions
-- statement:
--   Quadratic Fixed Point (Definition 3.1: a self-map $F$ of $[0,1]^d$ with coordinates given by monomials of degree at most two and rational coefficients of absolute value at most one; solutions $x = F(x)$) is FIXP-hard: every problem in FIXP admits a separable linear reduction to it,
--   $$\forall P \in \mathrm{FIXP}:\quad P \le_{SL} \text{Quadratic Fixed Point}.$$
--
--   It is the first of the three reductions; the paper proves it by encoding a three-player game into a quadratic map whose fixed points project onto Nash equilibria.
--
--   Differences from the source:
--   - generalization: FIXP: reducible to a fixed point of a circuit self-map of a cube (Definition 2.4) → InFIXP via the published basicFIXP, whose domain is any nonempty bounded rational polytope; reason: a cube is such a polytope, so the Lean class contains the paper's class and hardness for it implies hardness for the paper's class
--   - encoding: polynomial time (in the binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime over fixed injective encodings into the alphabet Sym (published FixpReciprocal_SLReduces); reason: the paper names no machine model; the reused FIXP framework fixes this one
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 6 (PDF 8), Theorem 3.2; proof §3.2, pp. 8–9 (PDF 10–11)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_HZFixp_Main_QFPProblem

open FixpReciprocal

namespace HZFixp.Main

/-- **Theorem 3.2.** Quadratic Fixed Point is FIXP-hard under SL reductions. -/
theorem theorem_3_2 : FIXPHard qfpProblem := by sorry

end HZFixp.Main
