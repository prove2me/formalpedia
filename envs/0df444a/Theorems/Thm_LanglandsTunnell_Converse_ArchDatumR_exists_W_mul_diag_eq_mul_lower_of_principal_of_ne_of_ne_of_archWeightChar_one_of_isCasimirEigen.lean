-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
-- name    : LanglandsTunnell.Converse.ArchDatumR.exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/deb37c7a-8106-570b-b3e7-6151ae731e94
-- title:
--   Reflection by diag(-1,1) as a lowering derivative
-- statement:
--   Fix $u_1,u_2\in\mathbb C$ and $a_1,a_2\in\mathbb Z/2$ with $a_1\neq a_2$ and $u_1\neq u_2$, subject to two further conditions on the parameter: for every nonzero integer $p$ with $u_1-u_2=p$ one has $a_1-a_2\neq p+1$ in $\mathbb Z/2$, and $|\operatorname{Re}(u_1-u_2)|<1$. Let $D$ be an `ArchDatumR` for the principal parameter $P=\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$, i.e. a function $W=D.W$ on $2\times 2$ real matrices which is smooth on the invertible locus, satisfies $W(\mathrm{unip}(x)g)=\psi(x)W(g)$ and the central law $W(zg)=\omega_P(z)|z|W(g)$ for $z\neq 0$, and comes equipped with entire zeta functions $\zeta(g,u,a,s)$ of finite order in vertical strips representing the zeta integrals of $W$ as $\mathrm{archFactor}$ of the twist $P(u,a)$ times $\zeta$, satisfying the functional equation with the archimedean $\varepsilon$-factor of $P(u,a)$ under $g\mapsto wg$, $(u,a,s)\mapsto(-(u+u_1+u_2),a+P.\mathrm{centralSign},1-s)$, together with the prescribed decay of all iterated derivatives in the coordinates $\mathrm{diag}(y,1)k$ for $|y|\geq 1$ and for $0<|y|\leq 1$. Assume moreover that $W$ has weight one under the row isometries, $W(xr)=\mathrm{archWeightChar}_{\mathbb R}(1)(r)\,W(x)$ for all $r$ in `rowIsometrySubgroup₀ ℝ` and $x\in GL_2(\mathbb R)$, and that $D$ satisfies the Casimir eigen-equation $-\bigl(\tfrac14 D_H^2W-\tfrac12 D_HW+D_ED_{F}W\bigr)(x)=\bigl(\tfrac14-((u_1-u_2)/2)^2\bigr)W(x)$ for all $x$ with $\det x\neq 0$, where $D_H,D_E,D_{F}$ denote differentiation at $t=0$ of $t\mapsto W(x\cdot\gamma(t))$ along the split torus, the upper unipotent and the lower unipotent one-parameter subgroups. Then there is a constant $\kappa\in\mathbb C$ such that for every $x$ with $\det x\neq 0$,
--   $$W\bigl(x\,\mathrm{diag}(-1,1)\bigr)=\kappa\,\bigl(D_HW(x)-i\,(D_EW(x)+D_{F}W(x))\bigr).$$
--
--   This is the archimedean matching identity for a weight-one Whittaker datum on $GL_2(\mathbb R)$: reflection by $\mathrm{diag}(-1,1)$ agrees, up to one global constant, with the lowering operator $D_H-i(D_E+D_F)$ applied to $W$. It feeds the identification of archimedean components of Whittaker coefficients in the converse-theorem input to Langlands–Tunnell, and is used in the two results comparing such a component with the weight-one archimedean Whittaker function of the parameter or its sign twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen.lean

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

theorem LanglandsTunnell.Converse.ArchDatumR.exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (hgen : ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (htype : |(u₁ - u₂).re| < 1)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) :
    ∃ κ : ℂ, ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      D.W (x * Matrix.diagonal ![(-1 : ℝ), 1]) =
        κ * (ArchCasimir.matrixFlowDeriv ArchDir.H D.W x -
              Complex.I * (ArchCasimir.matrixFlowDeriv ArchDir.E D.W x + ArchCasimir.matrixFlowDeriv ArchDir.Fm D.W x)) := by sorry
