-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_Supplement_lemma_3_4
-- name    : LowRandomnessDP.KNorm.Supplement.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:29:10.075583+00:00
-- url     : https://prove2.me/theorems/bcc540c3-9187-4646-b59a-fc6c8259f9fe
-- title:
--   Lemma 3.4 — fractional-part shift identity
-- statement:
--   Let $d\ge1$, $x\in\mathbb R^d$, and $a,b,m\in\{0,\ldots,d-1\}$ satisfy $b\equiv a-m\pmod d$. With $\Phi$ defined by Algorithm 1,
--
--   $$\Phi_b(x)-\Phi_a(x)=m-\left|\left\{i:\{x_i-a/d\}\ge1-m/d\right\}\right|.$$
--
--   This exact shift identity relates the finite minimization criterion to counts of coordinates near the end of a unit interval.
--
--   Differences from the source:
--   - encoding: one-based coordinate count and congruence $b\equiv a-m\pmod d$ → `Fin d` coordinates and shifts, real-cast finite cardinality, and `Int.ModEq` with integer subtraction; reason: the same index sets and exact integer congruence are retained without natural subtraction truncation
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), Lemma 3.4, PDF p. 12 / printed p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf; SHA-256 1562e70c55d785f992aaa32a161f0b06ac058da62f8f71fb07610037a20bc37b

import Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding

set_option autoImplicit false

open Classical

namespace LowRandomnessDP.KNorm.Supplement

/-- Lemma 3.4, PDF 12 / printed 10. Congruence uses integer subtraction. -/
theorem lemma_3_4 (d : ℕ) (hd : 0 < d) (x : Vec d) (a b m : Fin d)
    (hcong : Int.ModEq (d : ℤ) (b.val : ℤ) ((a.val : ℤ) - (m.val : ℤ))) :
    phi x b - phi x a = (m.val : ℝ) -
      ((Finset.univ.filter (fun i : Fin d =>
        1 - (m.val : ℝ) / d ≤ Int.fract (x i - (a.val : ℝ) / d))).card : ℝ) := by sorry

end LowRandomnessDP.KNorm.Supplement
