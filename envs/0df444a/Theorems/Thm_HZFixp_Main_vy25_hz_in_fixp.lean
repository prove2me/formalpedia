-- Prove2me | Theorems.Thm_HZFixp_Main_vy25_hz_in_fixp
-- name    : HZFixp.Main.vy25_hz_in_fixp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:27.433347+00:00
-- url     : https://prove2.me/theorems/e3db0f85-0d4f-48ca-9006-31b7f92c300a
-- title:
--   [VY25] (cited in §1.1) — exact HZ equilibrium computation belongs to FIXP
-- statement:
--   The search problem HZ Equilibrium (Definition 3.5) is in FIXP: it admits a separable linear reduction to the problem of finding a fixed point of a continuous self-map given by an algebraic circuit,
--   $$\text{HZ Equilibrium}\in\mathrm{FIXP}.$$
--
--   The paper cites this result of Vazirani and Yannakakis (2025) without proof; it is the membership half of Theorem 1.1.
--
--   Differences from the source:
--   - reading: FIXP over a cube (Definition 2.4) → InFIXP via the published basicFIXP over nonempty bounded rational polytopes; reason: Definition 2.4 is attributed to [EY10], whose FIXP is defined over such polytopes; [EY10] show the cube gives the same class
--   - encoding: polynomial time (in the binary encoding length) → Mathlib's Turing.TM2ComputableInPolyTime over fixed injective encodings into the alphabet Sym (published FixpReciprocal_SLReduces); reason: the paper names no machine model; the reused FIXP framework fixes this one
--   - encoding: a rational utility matrix v ∈ [0,1]^{n×n} in binary; solutions (X, p) and X → HZInst: n and n rows of n rationals in [0,1], binary (fNat, fRat); solution vectors (X_11,…,X_nn, p_1,…,p_n) of length n²+n and (X_11,…,X_nn) of length n², row-major; reason: Lean convention for the instances and real solution vectors of a search problem
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 1 (PDF 3), §1.1, citing [VY25]; used p. 7 (PDF 9), proof of Theorem 1.1

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_HZFixp_Main_HZProblem

open FixpReciprocal

namespace HZFixp.Main

/-- **[VY25], cited in §1.1.** Exact HZ equilibrium computation belongs to the class FIXP. -/
theorem vy25_hz_in_fixp : InFIXP hzProblem := by sorry

end HZFixp.Main
