-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_fourier_inversion
-- name    : OAI.SquareRootDegree.fourier_inversion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:33.876895+00:00
-- url     : https://prove2.me/theorems/06d1a5fb-8da8-4aa9-9eac-e95a9f62f3af
-- title:
--   Fourier inversion on the Boolean cube
-- statement:
--   Let $I$ be a finite index set and $\mathbb{B}=\{\mathrm{false},\mathrm{true}\}$, and read a point $x\in\mathbb{B}^I$ as a sign vector via $\operatorname{sgn}(\mathrm{false})=1$, $\operatorname{sgn}(\mathrm{true})=-1$. For $s\subseteq I$ let $\chi_s(x)=\prod_{i\in s}\operatorname{sgn}(x_i)$ be the Walsh character, and for $f:\mathbb{B}^I\to\mathbb{R}$ let
--   $$\hat f(s)=\frac{1}{2^{|I|}}\sum_{y\in\mathbb{B}^I}f(y)\,\chi_s(y)$$
--   be its Fourier coefficient (the uniform average of $f\chi_s$). Then for every function $f:\mathbb{B}^I\to\mathbb{R}$ and every point $x\in\mathbb{B}^I$,
--   $$f(x)=\sum_{s\subseteq I}\hat f(s)\,\chi_s(x).$$
--
--   Every real function on the cube is thus the linear combination of the characters with its Fourier coefficients as weights, so $f$ is determined by its coefficients. This is the basic tool for degree arguments: for instance, a function whose only possibly nonzero coefficient is $\hat f(\emptyset)$ is constant, the Fourier degree of a product is at most the sum of the degrees, and substituting coordinates does not increase the degree.
--
--   **Formalization Note** `Cube ι` is `ι → Bool`, `fourierCoeff f s` is the project's uniform `average` of `f x * character s x`, and the sum runs over all `s : Finset ι`. No nonemptiness assumption on `ι` is needed: for empty `ι` the cube has one point and the only subset is the empty one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Walsh.lean#L221-L236

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh

open OAI OAI.SquareRootDegree
open scoped BigOperators

theorem OAI.SquareRootDegree.fourier_inversion {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (x : Cube ι) :
    f x = ∑ s : Finset ι, fourierCoeff f s * character s x := by sorry
