-- Prove2me | Theorems.Thm_OAI_Cotype_fourier_oddPart
-- name    : OAI.Cotype.fourier_oddPart
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:49:41.371991+00:00
-- url     : https://prove2.me/theorems/29e9b66e-0de1-4c43-9623-71b0e0941a88
-- title:
--   Fourier coefficients of the odd part of a cube function
-- statement:
--   Let $\iota$ be a finite set and $f:\{0,1\}^\iota\to\mathbb R$. Let $\bar\varepsilon$ be the point with every coordinate flipped, and let $f_{\mathrm{odd}}(\varepsilon)=\frac12\bigl(f(\varepsilon)-f(\bar\varepsilon)\bigr)$ be the odd part. For a frequency $p$ with $|p|$ ones,
--   $$
--   \widehat{f_{\mathrm{odd}}}(p)=\frac{1-(-1)^{|p|}}{2}\,\hat f(p).
--   $$
--
--   So the odd part keeps exactly the Fourier coefficients of odd degree and removes the even ones.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/Fourier.lean#L72-L90

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier

open OAI OAI.Cotype
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem OAI.Cotype.fourier_oddPart (f : (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (oddPart f) p = (1 - paritySign p) / 2 * fourier f p := by sorry
