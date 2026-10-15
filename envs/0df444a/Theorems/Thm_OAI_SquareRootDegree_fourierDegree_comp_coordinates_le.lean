-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_fourierDegree_comp_coordinates_le
-- name    : OAI.SquareRootDegree.fourierDegree_comp_coordinates_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:43:46.455556+00:00
-- url     : https://prove2.me/theorems/7059d75e-2754-4427-8390-4b61257b2bde
-- title:
--   Substituting variables does not increase Fourier degree
-- statement:
--   Use the sign convention $\operatorname{sgn}(\mathsf{false})=1$, $\operatorname{sgn}(\mathsf{true})=-1$ on Boolean values. For a finite index set $I$ and $f:\{\mathsf{false},\mathsf{true}\}^I\to\mathbb R$, the Fourier coefficients are $\hat f(S)=\mathbb E_x\big[f(x)\chi_S(x)\big]$ with Walsh characters $\chi_S(x)=\prod_{i\in S}\operatorname{sgn}(x_i)$ and the uniform average $\mathbb E_x$ over the cube, and the Fourier degree is $\deg f=\max\{|S|:\hat f(S)\neq0\}$ (with $\deg f=0$ if all coefficients vanish).
--
--   Let $\iota$ and $\kappa$ be finite index sets, let $e:\iota\to\kappa$ be an arbitrary map, and let $f:\{\mathsf{false},\mathsf{true}\}^\iota\to\mathbb R$. Define $f_e:\{\mathsf{false},\mathsf{true}\}^\kappa\to\mathbb R$ by substituting the variable $x_{e(i)}$ for the $i$-th input, $f_e(x)=f\big((x_{e(i)})_{i\in\iota}\big)$. Then
--
--   $$
--   \deg f_e\le\deg f .
--   $$
--
--   The map $e$ need not be injective or surjective, so the statement covers renaming variables, identifying several variables with one another (where characters may collapse), and adding dummy variables. For example, a function applied to one block $x^{(j)}=(x_{(j,i)})_{i\in\gamma}$ of a larger cube $\{\mathsf{false},\mathsf{true}\}^{\kappa\times\gamma}$ has degree at most that of the original function.
--
--   **Formalization Note** In Lean $f_e$ is `fun x : Cube κ => f (fun i => x (e i))` and the degree is `fourierDegree`, the ordinary real Fourier degree.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Blocks.lean#L34-L53

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks

open OAI OAI.SquareRootDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.SquareRootDegree.fourierDegree_comp_coordinates_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : Cube ι → ℝ) (e : ι → κ) :
    fourierDegree (fun x : Cube κ => f (fun i => x (e i))) ≤ fourierDegree f := by sorry
