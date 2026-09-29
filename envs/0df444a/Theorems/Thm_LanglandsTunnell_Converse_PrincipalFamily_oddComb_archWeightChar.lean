-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_oddComb_archWeightChar
-- name    : LanglandsTunnell.Converse.PrincipalFamily.oddComb_archWeightChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/86e71a6d-1fd6-5cbb-bd8c-1558a994c50a
-- title:
--   Weight-one equivariance of the odd principal-series Whittaker combination
-- statement:
--   Fix complex parameters $u_1,u_2$. For a pair $(a_1,a_2)$ of classes in $\mathbb Z/2$ and a real $2\times 2$ matrix $g$, the project's principal-series Whittaker value is $\mathrm{Wmem}\,u_1\,u_2\,a_1\,a_2\,g = |\det g|\cdot \mathrm{quasiChar}\,u_1\,a_1(\det g)\cdot\int_{\mathbb R}\mathrm{innerW}\,a_1\,a_2\,g\,t\cdot \mathrm{quasiChar}\,(u_1-u_2)\,(a_1+a_2)(t)\,dt$, where $\mathrm{quasiChar}\,u\,a(y)=|y|^{u}$ times $1$ if $a=0$ and $\operatorname{sgn} y$ otherwise, and $\mathrm{innerW}\,a_1\,a_2\,h\,t=\int_{\mathbb R}\mathrm{phiStd}\,a_1\bigl(-t(h_{00}+x h_{10})\bigr)\,\mathrm{phiStd}\,a_2\bigl(-t(h_{01}+x h_{11})\bigr)\,\mathrm{psi}(-x)\,dx$, both integrals being Bochner integrals. The assertion is that for every $r$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $\mathrm{GL}_2(\mathbb R)$ and every $x\in\mathrm{GL}_2(\mathbb R)$, the combination $V(g)=\mathrm{Wmem}\,u_1\,u_2\,1\,0\,(g)+i\cdot\operatorname{sgn}(\det g)\cdot \mathrm{Wmem}\,u_1\,u_2\,0\,1\,(g)$, formed from the underlying matrices, satisfies $V(xr)=\mathrm{archWeightChar}_{\mathbb R}(1)(r)\cdot V(x)$, the value of `archWeightCharℝ` at the integer weight $1$ and at $r$ being coerced into $\mathbb C$.
--
--   This records the archimedean weight-one transformation behaviour: the odd combination of the two principal-series Whittaker functions with parameters $(a_1,a_2)=(1,0)$ and $(0,1)$ is equivariant under right translation by the row-isometry subgroup through the weight-one character `archWeightCharℝ`. It feeds the construction of an archimedean datum of weight one in [`LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero`](thm.html#LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero), which supplies the real-place input to the converse-theorem step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_PrincipalFamily_oddComb_archWeightChar.lean

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

theorem LanglandsTunnell.Converse.PrincipalFamily.oddComb_archWeightChar (u₁ u₂ : ℂ) :
    ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      Wmem u₁ u₂ 1 0 ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) +
          Complex.I * (((SignType.sign ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
            : ℝ) : ℂ) * Wmem u₁ u₂ 0 1 ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
        (archWeightCharℝ (1 : ℤ) r : ℂ) *
          (Wmem u₁ u₂ 1 0 (x : Matrix (Fin 2) (Fin 2) ℝ) +
            Complex.I * (((SignType.sign (x : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) *
              Wmem u₁ u₂ 0 1 (x : Matrix (Fin 2) (Fin 2) ℝ))) := by sorry
