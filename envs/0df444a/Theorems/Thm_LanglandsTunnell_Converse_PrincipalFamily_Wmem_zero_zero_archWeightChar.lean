-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_Wmem_zero_zero_archWeightChar
-- name    : LanglandsTunnell.Converse.PrincipalFamily.Wmem_zero_zero_archWeightChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/88898a13-1432-5f92-88f2-f8c511f5294a
-- title:
--   Right rotation invariance of the even principal Whittaker function
-- statement:
--   Fix complex parameters $u_1,u_2$. The assertion is that for every element $r$ of the subgroup `rowIsometrySubgroup₀ ℝ` of $\mathrm{GL}_2(\mathbb{R})$ and every $x\in\mathrm{GL}_2(\mathbb{R})$, the function `Wmem` with parameters $u_1,u_2$ and both parity indices equal to $0\in\mathbb{Z}/2$ satisfies $$\mathrm{Wmem}(x r)=\bigl(\mathrm{archWeightChar}_{\mathbb{R}}(0)(r)\bigr)\cdot \mathrm{Wmem}(x),$$ where the argument on each side is the underlying $2\times 2$ real matrix of the indicated element of $\mathrm{GL}_2(\mathbb{R})$ and the scalar is the value of the homomorphism `archWeightCharℝ` at the integer $0$ and at $r$, viewed in $\mathbb{C}$ through $\mathbb{C}^\times$. Here, for the parity indices $a_1=a_2=0$, the quasi-character factors `quasiChar` reduce to absolute-value powers, so that for a real matrix $g$ one has $$\mathrm{Wmem}(g)=|\det g|\cdot|\det g|^{u_1}\int_{\mathbb{R}}\Bigl(\int_{\mathbb{R}}\varphi_0\bigl(-t(g_{00}+x g_{10})\bigr)\,\varphi_0\bigl(-t(g_{01}+x g_{11})\bigr)\,\psi(-x)\,dx\Bigr)|t|^{u_1-u_2}\,dt,$$ with $\varphi_0=$ `phiStd 0`, both integrals Bochner integrals (hence $0$ when the integrand fails to be integrable). No hypotheses beyond membership of $r$ in `rowIsometrySubgroup₀ ℝ` are imposed; in particular no integrability is assumed.
--
--   This records the archimedean right transformation behaviour, under the rotation subgroup, of the explicit Whittaker function of the principal series in the even case, the weight-zero case of the relation $W(xr)=\chi_n(r)W(x)$. It is used in the construction of an archimedean datum with prescribed weight character, minimal type, Casimir eigenvalue and non-vanishing Whittaker function, namely by `exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_PrincipalFamily_Wmem_zero_zero_archWeightChar.lean

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

theorem LanglandsTunnell.Converse.PrincipalFamily.Wmem_zero_zero_archWeightChar (u₁ u₂ : ℂ) :
    ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      Wmem u₁ u₂ 0 0 ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (0 : ℤ) r : ℂ) * Wmem u₁ u₂ 0 0 (x : Matrix (Fin 2) (Fin 2) ℝ) := by sorry
