-- Prove2me | Theorems.Thm_NMAffExt_LBP_theorem_4_11
-- name    : NMAffExt.LBP.theorem_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:50.529887+00:00
-- url     : https://prove2.me/theorems/35fbebe1-b17b-48af-bd86-9aaa10ba75ed
-- title:
--   Theorem 4.11 — affine non-malleability implies $\mathrm{Corr}(f_u,P)\le\sqrt{2s(2\varepsilon+2^{-(n-k)})}$ for weakly read-once programs
-- statement:
--   Let $1\le k<n$ and let $F:\mathbb F_2^n\to\mathbb F_2^m$ be $(k,\varepsilon)$ non-malleable against globally fixed-point-free affine involutions (in particular, any $(k,\varepsilon)$ non-malleable affine extractor). For every nonzero $u\in\mathbb F_2^m$ and every weakly read-once linear branching program $P$ on $n$ bits with $s$ vertices,
--   $$\mathrm{Corr}(f_u,P)\le\sqrt{2s\bigl(2\varepsilon+2^{-(n-k)}\bigr)},\qquad f_u(x)=\langle u,F(x)\rangle.$$
--
--   This is the first statement of Theorem 1.6 in correlation notation.
--
--   Differences from the source:
--   - reading: "Let F be a $(k,\varepsilon)$ non-malleable affine extractor … It suffices to assume non-malleability against globally fixed-point-free affine involutions" → hypothesis `IsNMAffExtInv k ε F`; reason: the theorem's last sentence; this hypothesis is implied by `IsNMAffExt k ε F`, so the statement covers both sentences.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 59 (PDF 61), Theorem 4.11, eq. (4.9)

import Mathlib
import Definitions.Def_NMAffExt_LBP_Basic
import Definitions.Def_NMAffExt_LBP_NonMalleable
import Definitions.Def_NMAffExt_LBP_Program

namespace NMAffExt.LBP

/-- **Theorem 4.11.** Let `F` be `(k, ε)` non-malleable against globally fixed-point-free affine
involutions (in particular, a `(k, ε)` non-malleable affine extractor), `1 ≤ k < n`. For every nonzero
`u` and every size-`s` weakly read-once linear branching program `P`,
`Corr(f_u, P) ≤ √(2s(2ε + 2^{−(n−k)}))`. -/
theorem theorem_4_11 (n m k : ℕ) (ε : ℝ) (F : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hk : 1 ≤ k) (hkn : k < n) (hF : IsNMAffExtInv k ε F)
    (u : Fin m → ZMod 2) (hu : u ≠ 0) (s : ℕ) (P : Program n s) (hP : P.IsWeaklyReadOnce) :
    corr (parity F u) P.eval ≤ Real.sqrt (2 * s * (2 * ε + (2 : ℝ) ^ (-((n : ℤ) - k)))) := by sorry

end NMAffExt.LBP
