-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_discrete_of_archWeightChar_of_isCasimirEigen
-- name    : LanglandsTunnell.Converse.ArchDatumR.W_eq_zero_of_det_neg_of_discrete_of_archWeightChar_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/4d2685b0-bd66-5ae5-99b9-3a06a006b033
-- title:
--   Vanishing of the discrete-series Whittaker datum on det<0
-- statement:
--   Fix $u_0\in\mathbb C$ and $m\in\mathbb N$ with $1\le m$, and let $D$ be an archimedean Whittaker datum of type `ArchDatumR` for the real parameter `RealArchParam.discrete` $u_0\,m$: thus $D$ carries a function $W:M_2(\mathbb R)\to\mathbb C$, smooth on the invertible locus, satisfying $W(u(x)g)=\psi(x)W(g)$ for the upper unipotent, the central law $W(z\cdot g)=\chi_P(z)\,|z|\,W(g)$ for $z\neq0$, together with the attached family of zeta integrals (integrability beyond an abscissa, the identity $\int\text{zetaIntegrand}=\text{archFactor}(P.\mathrm{twist}\,u\,a)(s)\cdot\Xi(g,u,a,s)$ with $\Xi$ entire in $s$, the functional equation relating $\Xi$ at $(w g,-(u+2u_0),a+m+1,1-s)$ to $\epsilon\cdot\Xi(g,u,a,s)$, finite order in vertical strips, and the decay bounds for all derivatives near $y=0$ and $y=\infty$). Let $k\in\mathbb Z$ with $m+1\le k$, and assume: (i) $W$ transforms on the right under the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb R)$ by the character `archWeightCharℝ` $k$, i.e. $W(xr)=\mathrm{archWeightChar}_{\mathbb R}(k)(r)\,W(x)$ for all $r$ in that subgroup and all $x\in GL_2(\mathbb R)$; (ii) $W$ is a Casimir eigenfunction in the sense that for every $x$ with $\det x\neq0$, $-\bigl(\tfrac14 H^2W-\tfrac12 HW+E F W\bigr)(x)=\frac{1-m^2}{4}\,W(x)$, the derivatives being taken along the one-parameter flows attached to $H$, $E$, $F$. Then $W(x)=0$ for every $x\in M_2(\mathbb R)$ with $\det x<0$.
--
--   This is the archimedean input for the converse theorem in the discrete-series case: a Whittaker datum whose $SO(2)$-weight exceeds the lowest weight $m+1$ of the parameter must vanish identically on the component of negative determinant, because the decaying solution of the corresponding Whittaker equation has a Mellin transform with a pole that the datum's zeta identity forbids. It is used downstream in the cubic-induction step and in the identification of the archimedean factor of Whittaker coefficients of weight-one cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_discrete_of_archWeightChar_of_isCasimirEigen.lean

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

theorem LanglandsTunnell.Converse.ArchDatumR.W_eq_zero_of_det_neg_of_discrete_of_archWeightChar_of_isCasimirEigen
    (u₀ : ℂ) (m : ℕ) (hm : 1 ≤ m) (D : ArchDatumR (RealArchParam.discrete u₀ m hm)) (k : ℤ)
    (hk : (m : ℤ) + 1 ≤ k)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det < 0) :
    D.W x = 0 := by sorry
