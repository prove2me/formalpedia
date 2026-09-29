-- Prove2me | Theorems.Thm_GeneralCK_Noise_hasDerivAt_applyNoise
-- name    : GeneralCK.Noise.hasDerivAt_applyNoise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T21:51:35.989402+00:00
-- url     : https://prove2.me/theorems/597410ee-f58c-47ca-b5de-10cfb7d818d7
-- title:
--   The Boolean noise flow has the coordinate-difference generator
-- statement:
--   Let $v:\{0,1\}^n\to\mathbb R$, let $y$ be a cube point, and let $p(t)=(1-e^{-2t})/2$. If $y^{(i)}$ denotes $y$ with coordinate $i$ flipped, then for every real $t$, $$\frac{d}{dt}T_{p(t)}v(y)=\sum_{i=1}^n\bigl(T_{p(t)}v(y^{(i)})-T_{p(t)}v(y)\bigr).$$ This finite-sum derivative identifies the generator used in the entropy-flow argument.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/NoiseEvolution.lean#L56-L66

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_noise_evolution
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
open GeneralCK GeneralCK.Noise

theorem GeneralCK.Noise.hasDerivAt_applyNoise {n : ℕ} (v : Cube n → ℝ) (y : Cube n) (t : ℝ) :
    HasDerivAt (fun s => applyNoise (crossover s) v y)
      (∑ i, (applyNoise (crossover t) v (flip y i) - applyNoise (crossover t) v y)) t := by sorry
