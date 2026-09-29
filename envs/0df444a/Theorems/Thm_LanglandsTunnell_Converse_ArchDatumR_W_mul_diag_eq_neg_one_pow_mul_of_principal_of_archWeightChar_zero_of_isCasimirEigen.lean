-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
-- name    : LanglandsTunnell.Converse.ArchDatumR.W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/adbcda13-8d6f-58c3-9325-16889e0dbf3c
-- title:
--   Reflection law for weight-zero real principal Whittaker data
-- statement:
--   Let $u_1,u_2\in\mathbb C$ and $a\in\mathbb Z/2$, and assume $u_1-u_2$ is not an odd integer, i.e. $u_1-u_2\neq p$ for every odd $p\in\mathbb Z$. Let $D$ be an `ArchDatumR` for the real principal archimedean parameter $\mathrm{principal}\,u_1\,a\,u_2\,a$ (both signs equal to $a$): thus $D$ consists of a function $W:M_2(\mathbb R)\to\mathbb C$ that is $C^\infty$ on the invertible matrices, satisfies the unipotent law $W(\mathrm{unip}(x)g)=\psi(x)W(g)$ and the central law $W(zg)=\omega_P(z)\,|z|\,W(g)$ for $z\neq0$, together with a family of functions $\mathrm{zetaEntire}(g,u,a,s)$, entire in $s$, whose values compute the Mellin-type integrals of $W$ along the torus as $\mathrm{archFactor}(P.\mathrm{twist}\,u\,a)(s)\cdot\mathrm{zetaEntire}(g,u,a,s)$ in the convergent range, which satisfy the functional equation with $\epsilon$-factor $\mathrm{epsilonFactor}(P.\mathrm{twist}\,u\,a)$ relating $s$ to $1-s$ and $g$ to $\mathrm{weyl}\cdot g$, are of finite order in vertical strips, and for which $W$ obeys the prescribed rapid decay at infinity and growth control at $0$ along the torus times $K$ coordinates. Assume further that $W$ is right equivariant for the weight-zero character $\mathrm{archWeightChar}_{\mathbb R}\,0$ of the group `rowIsometrySubgroup₀ ℝ`, namely $W(x r)=\mathrm{archWeightChar}_{\mathbb R}\,0\,(r)\cdot W(x)$ for all $r$ in that group and all $x\in GL_2(\mathbb R)$, and that $D$ satisfies the Casimir eigenvalue equation: $\mathrm{matrixCasimir}\,W\,x=\bigl(\tfrac14-((u_1-u_2)/2)^2\bigr)W(x)$ for all $x$ with $\det x\neq0$, where $\mathrm{matrixCasimir}$ is the second-order differential operator $-\bigl(\tfrac14 H^2-\tfrac12 H+EF^-\bigr)$ formed from the one-parameter flow derivatives in the directions $H$, $E$, $F^-$. Then for every $x\in M_2(\mathbb R)$ with $\det x\neq0$ one has $W\bigl(x\cdot\mathrm{diag}(-1,1)\bigr)=(-1)^{a.\mathrm{val}}\,W(x)$.
--
--   This is the reflection (sign) law for a weight-zero Whittaker function attached to a real principal series with equal signs at the two characters: right translation by $\mathrm{diag}(-1,1)$ multiplies the function by $(-1)^a$, the genericity hypothesis on $u_1-u_2$ excluding the degenerate parameters. It feeds the archimedean side of the converse-theorem input to Langlands–Tunnell, being used in the cubic induction step and in the identification of archimedean Whittaker fibres with the datum $W$ up to a sign twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
    (u₁ u₂ : ℂ) (a : ZMod 2)
    (hgen : ∀ p : ℤ, Odd p → u₁ - u₂ ≠ (p : ℂ))
    (D : ArchDatumR (RealArchParam.principal u₁ a u₂ a))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    D.W (x * Matrix.diagonal ![(-1 : ℝ), 1]) = (-1 : ℂ) ^ a.val * D.W x := by sorry
