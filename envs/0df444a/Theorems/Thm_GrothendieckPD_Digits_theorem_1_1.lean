-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_theorem_1_1
-- name    : GrothendieckPD.Digits.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:45.236211+00:00
-- url     : https://prove2.me/theorems/fd1c7fb4-86e8-42e4-b739-fe3afd390684
-- title:
--   Theorem 1.1: $1.773\le K_G\le1.7799$
-- statement:
--   Let
--   $$\mathrm{OPT}(A)=\max_{x_i,y_j\in\{-1,1\}}\sum_{i,j}A_{ij}x_iy_j,\qquad \mathrm{SDP}(A)=\sup_{\|u_i\|=\|v_j\|=1}\sum_{i,j}A_{ij}\langle u_i,v_j\rangle$$
--   for $A\in\mathbb R^{m\times n}$, and let the real Grothendieck constant be
--   $$K_G=\sup_{m,n\in\mathbb N}\ \sup_{A\in\mathbb R^{m\times n}}\frac{\mathrm{SDP}(A)}{\mathrm{OPT}(A)}.\qquad(1.1)$$
--   Then
--   $$1.773\le K_G\le1.7799 .$$
--
--   The theorem determines the hundredths digit of $K_G$: its first three digits are $1.77$.
--
--   Differences from the source:
--   - encoding: K_G = sup_{m,n} sup_{A} SDP(A)/OPT(A) (Eq. 1.1) → K_G = inf{K : SDP(A) ≤ K·OPT(A) for all real matrices A} (published GrothendieckConstant.grothendieckConst), with unit vectors in ℝ^d for arbitrary d; reason: same value: the ratio is undefined only at A = 0, where both sides vanish; OPT(A) > 0 for A ≠ 0; the admissible set is nonempty (Grothendieck's inequality) and bounded below; unit vectors in any dimension give the same SDP value as in ℝ^{m+n}
--   - encoding: decimal constants → exact rationals; reason: the source says every decimal is exact
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Theorem 1.1 and Eq. (1.1), p. 1

import Mathlib
import Definitions.Def_GrothendieckConstantDefs

namespace GrothendieckPD.Digits

/-- Theorem 1.1 (Heilman–Jones–Malavolta, STOC 2027 submission #820, p. 1):
`1.773 ≤ K_G ≤ 1.7799` for the real Grothendieck constant `K_G` of Eq. (1.1). -/
theorem theorem_1_1 :
    (1773 / 1000 : ℝ) ≤ GrothendieckConstant.grothendieckConst ∧
      GrothendieckConstant.grothendieckConst ≤ 17799 / 10000 := by sorry

end GrothendieckPD.Digits
