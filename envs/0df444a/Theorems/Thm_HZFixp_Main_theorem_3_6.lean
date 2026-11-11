-- Prove2me | Theorems.Thm_HZFixp_Main_theorem_3_6
-- name    : HZFixp.Main.theorem_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:20.669667+00:00
-- url     : https://prove2.me/theorems/3ce23292-bdfd-4f4a-885c-737858fa5c34
-- title:
--   Theorem 3.6 — HZ Equilibrium is FIXP-hard under SL reductions, even for the allocation alone
-- statement:
--   HZ Equilibrium (Definition 3.5: rational $v\in[0,1]^{n\times n}$ in binary; solutions the HZ equilibria $(X,p)$ of Definition 2.1) is FIXP-hard under separable linear reductions, and so is its allocation-only version (solutions the allocations $X$ for which some $p$ makes $(X,p)$ an HZ equilibrium):
--   $$\forall P\in\mathrm{FIXP}:\quad P\le_{SL}\text{HZ Equilibrium}\quad\text{and}\quad P\le_{SL}\text{HZ allocation}.$$
--
--   It is the last reduction; with [VY25] it gives Theorem 1.1.
--
--   Differences from the source:
--   - generalization: FIXP: reducible to a fixed point of a circuit self-map of a cube (Definition 2.4) → InFIXP via the published basicFIXP, whose domain is any nonempty bounded rational polytope; reason: a cube is such a polytope, so the Lean class contains the paper's class and hardness for it implies hardness for the paper's class
--   - encoding: polynomial time (in the binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime over fixed injective encodings into the alphabet Sym (published FixpReciprocal_SLReduces); reason: the paper names no machine model; the reused FIXP framework fixes this one
--   - encoding: a rational utility matrix v ∈ [0,1]^{n×n} in binary; solutions (X, p) and X → HZInst: n and n rows of n rationals in [0,1], binary (fNat, fRat); solution vectors (X_11,…,X_nn, p_1,…,p_n) of length n²+n and (X_11,…,X_nn) of length n², row-major; reason: Lean convention for the instances and real solution vectors of a search problem
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 7 (PDF 9), Theorem 3.6; proof pp. 25–26 (PDF 27–28)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_HZFixp_Main_HZProblem

open FixpReciprocal

namespace HZFixp.Main

/-- **Theorem 3.6.** HZ Equilibrium is FIXP-hard under SL reductions, even when only the
equilibrium allocation is requested. -/
theorem theorem_3_6 : FIXPHard hzProblem ∧ FIXPHard hzAllocProblem := by sorry

end HZFixp.Main
