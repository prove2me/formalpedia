-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_Supplement_lemma_3_5
-- name    : LowRandomnessDP.KNorm.Supplement.lemma_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:29:44.72719+00:00
-- url     : https://prove2.me/theorems/a0135351-f823-4ae9-b03f-d574b551e20d
-- title:
--   Lemma 3.5 — coordinate tail count
-- statement:
--   Let $d\ge1$ and $x\in\mathbb R^d$, and let $A(x)$ be the smallest shift minimizing $\Phi$. For every $\theta\in[0,1]$,
--
--   $$\left|\left\{i:\{x_i-A(x)/d\}\ge1-\theta\right\}\right|\le d\theta+1.$$
--
--   Both endpoints are included. The estimate controls how many rounded coordinates can take the lower of two possible floor values in a small ball.
--
--   Differences from the source:
--   - encoding: one-based coordinate count with $d,x$ fixed in the section → `Fin d` coordinates with finite cardinality cast to a real number and explicit universal $d\ge1,x$; reason: the finite index set is relabelled and the standing assumptions are written explicitly
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), Lemma 3.5, PDF p. 12 / printed p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf; SHA-256 1562e70c55d785f992aaa32a161f0b06ac058da62f8f71fb07610037a20bc37b

import Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding

set_option autoImplicit false

open Classical

namespace LowRandomnessDP.KNorm.Supplement

/-- Lemma 3.5, PDF 12 / printed 10. Both endpoints of [0,1] are included. -/
theorem lemma_3_5 (d : ℕ) (hd : 0 < d) (x : Vec d)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ((Finset.univ.filter (fun i : Fin d =>
      1 - θ ≤ Int.fract (x i - ((A hd x).val : ℝ) / d))).card : ℝ) ≤
      (d : ℝ) * θ + 1 := by sorry

end LowRandomnessDP.KNorm.Supplement
