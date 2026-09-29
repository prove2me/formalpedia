-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_DiscreteFamily_W_archWeightChar
-- name    : LanglandsTunnell.Converse.DiscreteFamily.W_archWeightChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/3b4dbc5c-ed7e-5a26-b13c-e1870c2875d7
-- title:
--   Right rotation equivariance of the discrete-series Whittaker function
-- statement:
--   Fix a complex number $u_0$ and a natural number $k_0$, and let $W_{u_0,k_0}$ denote [`LanglandsTunnell.Converse.DiscreteFamily.W u₀ k₀`](def/LanglandsTunnell_Converse_ExplicitWhittakerFunctions.html#L40), the explicit discrete-series Whittaker function on real $2\times 2$ matrices attached to these parameters. The assertion is that for every element $r$ of the subgroup `rowIsometrySubgroup₀ ℝ` of $\mathrm{GL}_2(\mathbb R)$ and every $x \in \mathrm{GL}_2(\mathbb R)$, the value of $W_{u_0,k_0}$ on the matrix underlying the product $x\,r$ equals $\chi(r)\cdot W_{u_0,k_0}(x)$, where $\chi =$ `archWeightCharℝ ((k₀ : ℤ) + 1)` is the archimedean weight character of weight $k_0+1$, a homomorphism into $\mathbb C^{\times}$ whose unit value at $r$ is regarded as a complex number; concretely, writing $a = r_{00}$ and $b = r_{01}$, that value is $(a + ib)^{k_0+1}$. Membership of $r$ in `rowIsometrySubgroup₀ ℝ` is used only through the entry relations $r_{10} = -r_{01}$, $r_{11} = r_{00}$ and $r_{00}^2 + r_{01}^2 = 1$, i.e. $r$ is a rotation matrix.
--
--   This is the archimedean weight (lowest-weight, $K$-type) transformation law of the discrete-series Whittaker function under right translation by the rotation subgroup $\mathrm{SO}(2) \subset \mathrm{GL}_2(\mathbb R)$. It is one of the properties of the explicit discrete-series family used in the converse-theorem input to Langlands–Tunnell, and is cited in the construction of an archimedean datum with prescribed weight character, minimal type, Casimir eigenvalue and non-vanishing $W$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_DiscreteFamily_W_archWeightChar.lean

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

theorem LanglandsTunnell.Converse.DiscreteFamily.W_archWeightChar (u₀ : ℂ) (k₀ : ℕ) :
    ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      W u₀ k₀ ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ ((k₀ : ℤ) + 1) r : ℂ) * W u₀ k₀ (x : Matrix (Fin 2) (Fin 2) ℝ) := by sorry
