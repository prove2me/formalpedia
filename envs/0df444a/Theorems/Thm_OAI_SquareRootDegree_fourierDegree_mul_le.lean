-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_fourierDegree_mul_le
-- name    : OAI.SquareRootDegree.fourierDegree_mul_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:59.857856+00:00
-- url     : https://prove2.me/theorems/8a46fd20-b35e-4baf-861c-ddf5a5b0511f
-- title:
--   Fourier degree is subadditive under pointwise products on the Boolean cube
-- statement:
--   Let $\iota$ be a finite index set and let $\mathcal C_\iota=\{\mathsf{false},\mathsf{true}\}^\iota$ be the Boolean cube, where a Boolean value is read as a sign via $\operatorname{sgn}(\mathsf{false})=1$ and $\operatorname{sgn}(\mathsf{true})=-1$. For $S\subseteq\iota$ let $\chi_S(x)=\prod_{i\in S}\operatorname{sgn}(x_i)$ be the Walsh character, and for $f:\mathcal C_\iota\to\mathbb R$ let $\hat f(S)=\mathbb E_x\big[f(x)\,\chi_S(x)\big]$ be its Fourier coefficient, where $\mathbb E_x$ is the uniform average over the $2^{|\iota|}$ points of the cube. The (real) Fourier degree of $f$ is $\deg f=\max\{|S| : S\subseteq\iota,\ \hat f(S)\neq0\}$, with $\deg f=0$ when all coefficients vanish.
--
--   For all functions $f,g:\mathcal C_\iota\to\mathbb R$, the pointwise product $fg$ satisfies
--
--   $$
--   \deg(fg)\le\deg f+\deg g .
--   $$
--
--   This is the multiplicative rule of the degree calculus for real-valued functions on the cube: products of low-degree functions stay of controlled degree. It is used to bound the Fourier degree of functions assembled as products of simpler pieces, for instance indicators of joint events $\{F_1=b_1,\dots,F_k=b_k\}$ written as products of single indicators.
--
--   **Formalization Note** The cube is `Cube ι = ι → Bool`, coefficients are `fourierCoeff f s`, and `fourierDegree f` is the `Finset.sup` of `Finset.card` over the sets with nonzero coefficient, so the zero function has degree $0$. This is the ordinary real Fourier degree, not the degree over $\mathbb F_2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Walsh.lean#L377-L413

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh

open OAI OAI.SquareRootDegree
open scoped BigOperators

theorem OAI.SquareRootDegree.fourierDegree_mul_le {ι : Type*} [Fintype ι] (f g : Cube ι → ℝ) :
    fourierDegree (fun x => f x * g x) ≤ fourierDegree f + fourierDegree g := by sorry
