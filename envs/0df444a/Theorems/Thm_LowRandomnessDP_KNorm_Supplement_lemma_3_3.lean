-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_Supplement_lemma_3_3
-- name    : LowRandomnessDP.KNorm.Supplement.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:28:34.318614+00:00
-- url     : https://prove2.me/theorems/2754874a-56ca-4506-945a-1c2b208efc4a
-- title:
--   Lemma 3.3 — rounding error
-- statement:
--   Let $d\ge1$ and $x\in\mathbb R^d$, and let $R$ be Algorithm 1 with the smallest minimizing shift. Then
--
--   $$\|R(x)-x\|_\infty\le1.$$
--
--   This supplies the common representative radius for the concrete partition at every scale.
--
--   Differences from the source:
--   - encoding: coordinates $1,\ldots,d$ and the sup-norm bound → coordinates `Fin d` and all coordinate absolute errors at most one; reason: these are equivalent for each positive finite dimension
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), Lemma 3.3, PDF p. 11 / printed p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf; SHA-256 1562e70c55d785f992aaa32a161f0b06ac058da62f8f71fb07610037a20bc37b

import Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding

set_option autoImplicit false

open Classical

namespace LowRandomnessDP.KNorm.Supplement

/-- Lemma 3.3, PDF 11 / printed 9: the coordinate form of the sup-norm bound. -/
theorem lemma_3_3 (d : ℕ) (hd : 0 < d) (x : Vec d) :
    ∀ i, |R hd x i - x i| ≤ 1 := by sorry

end LowRandomnessDP.KNorm.Supplement
