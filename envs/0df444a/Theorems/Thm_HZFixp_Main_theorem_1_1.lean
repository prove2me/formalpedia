-- Prove2me | Theorems.Thm_HZFixp_Main_theorem_1_1
-- name    : HZFixp.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:22.329806+00:00
-- url     : https://prove2.me/theorems/f296371f-a629-4d47-908d-f3275ed388ee
-- title:
--   Theorem 1.1 — computing an exact HZ equilibrium is FIXP-complete; FIXP-hard already for the allocation
-- statement:
--   Let HZ Equilibrium be the search problem whose instances are the rational utility matrices $v\in[0,1]^{n\times n}$ (binary) and whose solutions are the HZ equilibria $(X,p)$: $X\in B_n$, $p\ge0$, $p\cdot X_i\le1$ and $v_i\cdot X_i=\mathrm{OPT}_i(p)$ for every agent (Definition 2.1). Then HZ Equilibrium is **FIXP-complete** under separable linear reductions, and the problem that asks only for the allocation $X$ of some HZ equilibrium is **FIXP-hard**:
--   $$\text{HZ Equilibrium is FIXP-complete}\qquad\text{and}\qquad\text{HZ allocation is FIXP-hard}.$$
--
--   This settles the conjecture of Vazirani and Yannakakis: exact HZ equilibrium computation is as hard as three-player Nash equilibrium.
--
--   Differences from the source:
--   - reading: FIXP over a cube (Definition 2.4) → InFIXP via the published basicFIXP over nonempty bounded rational polytopes; reason: Definition 2.4 is attributed to [EY10], whose FIXP is defined over such polytopes; [EY10] show the cube gives the same class
--   - generalization: FIXP: reducible to a fixed point of a circuit self-map of a cube (Definition 2.4) → InFIXP via the published basicFIXP, whose domain is any nonempty bounded rational polytope; reason: a cube is such a polytope, so the Lean class contains the paper's class and hardness for it implies hardness for the paper's class
--   - encoding: polynomial time (in the binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime over fixed injective encodings into the alphabet Sym (published FixpReciprocal_SLReduces); reason: the paper names no machine model; the reused FIXP framework fixes this one
--   - encoding: a rational utility matrix v ∈ [0,1]^{n×n} in binary; solutions (X, p) and X → HZInst: n and n rows of n rationals in [0,1], binary (fNat, fRat); solution vectors (X_11,…,X_nn, p_1,…,p_n) of length n²+n and (X_11,…,X_nn) of length n², row-major; reason: Lean convention for the instances and real solution vectors of a search problem
--   - reading: 'a market with rational utilities' → the instances of Definition 3.5: any n and any rational v ∈ [0,1]^{n×n}, without the §2 normalization; reason: the proof of Theorem 1.1 (p. 7) is about Definition 3.5's problem
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 2 (PDF 4), Theorem 1.1; proof p. 7 (PDF 9)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_HZFixp_Main_HZProblem

open FixpReciprocal

namespace HZFixp.Main

/-- **Theorem 1.1.** Computing an exact Hylland–Zeckhauser equilibrium for a market with rational
utilities is FIXP-complete under the separable linear reduction. The hardness already holds when
only the equilibrium allocation is requested. -/
theorem theorem_1_1 : FIXPComplete hzProblem ∧ FIXPHard hzAllocProblem := by sorry

end HZFixp.Main
