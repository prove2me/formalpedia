-- Prove2me | Theorems.Thm_OAI_Cotype_fourier_inversion
-- name    : OAI.Cotype.fourier_inversion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:48:36.733177+00:00
-- url     : https://prove2.me/theorems/975dce78-2e1d-4645-bd3c-2facfc0fa874
-- title:
--   Fourier inversion on the discrete cube
-- statement:
--   Let $\iota$ be a finite set and $f:\{0,1\}^\iota\to\mathbb R$. For $p,\varepsilon\in\{0,1\}^\iota$ let $\chi_p(\varepsilon)=\prod_{i:\,p_i=1}s(\varepsilon_i)$, where $s(0)=1$ and $s(1)=-1$. Let $\hat f(p)=\mathbb E_\varepsilon f(\varepsilon)\chi_p(\varepsilon)$ be the Fourier coefficient, with $\mathbb E$ the uniform average. Then for every $\varepsilon$,
--   $$
--   \sum_{p}\hat f(p)\,\chi_p(\varepsilon)=f(\varepsilon).
--   $$
--
--   Every real function on the cube is the sum of its Walsh expansion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/Cube.lean#L59-L81

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube

open OAI OAI.Cotype
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem OAI.Cotype.fourier_inversion (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    (∑ p, fourier f p * character p ε) = f ε := by sorry
