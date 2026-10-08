-- Prove2me | Theorems.Thm_McLeishCLT_MDA_exp_approx
-- name    : McLeishCLT.MDA.exp_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:08:40.225468+00:00
-- url     : https://prove2.me/theorems/0855c5d5-83f3-42b7-9c75-440e145b9195
-- title:
--   p. 621, proof of (2.1) — e^{ix} = (1 + ix)exp{−x²/2 + r(x)} with |r(x)| ≤ |x|³ for |x| < 1
-- statement:
--   Let $r(x)=ix+x^2/2-\log(1+ix)$ for real $x$, with the principal logarithm. Then for every real $x$
--   $$e^{ix}=(1+ix)\exp\Big\{-\frac{x^2}{2}+r(x)\Big\},$$
--   and if moreover $|x|<1$, then
--   $$|r(x)|\le|x|^3.$$
--
--   This is the approximation on which McLeish's characteristic-function argument rests: it rewrites $e^{itS_n}$ as the product $T_n$ times a Gaussian factor and a remainder that is cubic in the summands.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 621, proof of Theorem (2.1), first sentence

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- p. 621, proof of (2.1): `e^{ix} = (1 + ix) exp{-x²/2 + r(x)}`, and `|r(x)| ≤ |x|³` for `|x| < 1`. -/
theorem exp_approx (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (1 + Complex.I * (x : ℂ)) * Complex.exp (-(x : ℂ) ^ 2 / 2 + remR x) ∧
      (|x| < 1 → ‖remR x‖ ≤ |x| ^ 3) := by sorry

end McLeishCLT.MDA
