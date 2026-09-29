-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen
-- name    : LanglandsTunnell.Converse.ArchDatumR.W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/8e0bbb42-99db-5414-be54-7942fa2ec454
-- title:
--   Weight-one limit-of-discrete-series datum vanishes on negative determinants
-- statement:
--   Fix $u_0 \in \mathbb{C}$ and $a_1, a_2 \in \mathbb{Z}/2$ with $a_1 \neq a_2$, and let $D$ be an `ArchDatumR` for the real archimedean parameter $\mathrm{principal}\ u_0\ a_1\ u_0\ a_2$, i.e. a function $W : M_2(\mathbb{R}) \to \mathbb{C}$, smooth on the invertible locus, satisfying the unipotent law $W(n(x)g) = \psi(x)W(g)$ and the central law $W(zg) = \chi_P(z)\,|z|\,W(g)$ for $z \neq 0$, together with a family of auxiliary functions $\zeta(g,u,a,\cdot)$ that are entire in $s$, of finite order in vertical strips, represent the zeta integrals of $W$ as $(P.\mathrm{twist}\ u\ a).\mathrm{archFactor}(s)$ times $\zeta(g,u,a,s)$ in a right half plane, satisfy the functional equation relating $\zeta$ at $1-s$ after applying the Weyl element to $\varepsilon(P.\mathrm{twist}\ u\ a)\,\zeta(g,u,a,s)$, and obey prescribed decay bounds for all derivatives near $0$ and near $\infty$ along the torus-times-maximal-compact coordinates. Assume in addition that $W$ has weight one for the subgroup `rowIsometrySubgroup₀ ℝ` of $\mathrm{GL}_2(\mathbb{R})$ (row isometries, in the sense of `IsRowIsometry`: $\|\det k\| = 1$ and the two coordinate forms preserve the Euclidean norm), namely $W(xr) = \mathrm{archWeightChar}_{\mathbb{R}}(1)(r)\,W(x)$ for all such $r$ and all $x \in \mathrm{GL}_2(\mathbb{R})$, and that $D$ satisfies `ArchCasimir.IsCasimirEigen`: the matrix Casimir operator $-\bigl(\tfrac14 \partial_H^2 - \tfrac12 \partial_H + \partial_E \partial_{F^-}\bigr)$ applied to $W$ equals the parameter's Laplace eigenvalue $\tfrac14 - ((u_0-u_0)/2)^2 = \tfrac14$ times $W$ at every $x$ with $\det x \neq 0$. The conclusion is that $W(x) = 0$ for every real $2\times 2$ matrix $x$ with $\det x < 0$.
--
--   This is the archimedean vanishing statement for the limit of discrete series in the converse-theorem input: a weight-one Whittaker datum with Laplace eigenvalue $\tfrac14$ and equal exponents but opposite signs is supported on the positive-determinant sheet. It is used in the construction of the weight-one archimedean Whittaker function and in identifying the Whittaker coefficients of the relevant cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen.lean

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

theorem LanglandsTunnell.Converse.ArchDatumR.W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen
    (u₀ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (D : ArchDatumR (RealArchParam.principal u₀ a₁ u₀ a₂))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det < 0) :
    D.W x = 0 := by sorry
