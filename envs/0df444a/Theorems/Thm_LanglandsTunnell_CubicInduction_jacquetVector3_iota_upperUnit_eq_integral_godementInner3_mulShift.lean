-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/c590a536-61e7-56c0-9022-7ba0cc47bfef
-- title:
--   Jacquet vector at a real diagonal torus element, unfolded
-- statement:
--   Fix a real archimedean parameter $P$ and an archimedean datum $D$ for $P$ (so in particular a Whittaker function $D.W$ on $2\times 2$ real matrices), a complex number $u_3$, a sign $a_3 \in \mathbb{Z}/2$, a real dilation parameter $a$, an additive character $\psi$ of the infinite adele ring of $\mathbb{Q}$, a function $S$ on the real $2\times 3$ matrices with complex values, and nonzero reals $a_1, a_2$. Let $q \in \mathrm{GL}_2(\mathbb{R})$ be the invertible matrix $!![a_1,0;0,a_2]$ given by `upperUnit a₁ 0 a₂`, let it be placed at the (unique, real) infinite place of $\mathbb{Q}$ by `archRealGLAt`, embedded into adelic $\mathrm{GL}_3$ by `iota`, and let $g$ be its archimedean component in $\mathrm{GL}_3$ of the infinite adeles. The assertion is that $\mathtt{jacquetVector3}\,D\,u_3\,a_3\,a\,\psi\,S$ at $g$ — by definition $\chi_{u_3+1,a_3}(\det \mathrm{realMat}(g))$ times the integral over $e \in M_2(\mathbb{R})$ of `jacquetIntegrand3` — equals
--   $$\int_{M_2(\mathbb{R})} \Bigl(\int_{\mathbb{R}^2} S\bigl(e\cdot[\,1\mid v\,]\bigr)\,\psi\bigl(a_2\cdot(-v_1)\bigr)\,dv\Bigr)\;\chi_{u_3+2,a_3}(\det e)\;|\det e|^{-2}\;D.W\bigl(\mathrm{diag}(a,1)\,q\,e^{-1}\bigr)\,de,$$
--   where the inner factor is `godementInner3` for the multiplicatively shifted character $x \mapsto \psi(\mathtt{ofReal}(a_2)\,x)$ at the pair $(e,1)$, the $2\times 3$ matrix being $e$ applied to the rows $(1,0,v_0)$, $(0,1,v_1)$, and $\chi_{u,b}(y) = |y|^{u}$ times $\mathrm{sign}(y)$ when $b \neq 0$. In particular the prefactor $\chi_{u_3+1,a_3}$ has disappeared on the right-hand side.
--
--   This is the pointwise unfolding of the Jacquet–Godement vector of the third line at the image of a diagonal element of $\mathrm{GL}_2(\mathbb{R})$: the two linear changes of variable hidden in the definition have been carried out, so that the Godement inner kernel is evaluated at the identity and the torus enters only through the shift of $\psi$ and the argument of the Whittaker function. It feeds the Rankin–Selberg computation expressing the Jacquet vector on torus pairs as an integral of a quasi-character against a torus integral and a Godement–Mellin transform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift
    {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    jacquetVector3 D u₃ a₃ a ψ S
        (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ
          (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
            (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂)))) =
      ∫ e : Fin 2 → Fin 2 → ℝ,
        godementInner3 (ψ.mulShift (AutomorphicForm.StandardKernel.ofReal a₂)) S (Matrix.of e) 1 *
          ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            D.W (ArchR.diagOne a * !![a₁, 0; 0, a₂] * (Matrix.of e)⁻¹) := by sorry
