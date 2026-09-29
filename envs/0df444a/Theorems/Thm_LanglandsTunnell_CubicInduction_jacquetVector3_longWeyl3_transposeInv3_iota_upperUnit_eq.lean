-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/ac68274f-ed82-5f15-b3d9-dca0c5948643
-- title:
--   Dual Jacquet vector at a Siegel upper-unit torus point
-- statement:
--   Fix a real archimedean parameter $P_2$ and an archimedean $GL_2$ Whittaker datum $D$ for it (a function $W$ on real $2\times 2$ matrices satisfying the smoothness, unipotent-equivariance, central-character, and zeta-integral axioms of `ArchDatumR`), a complex exponent $u_3$, a sign $a_3 \in \mathbb{Z}/2$, a real number $a$, an additive character $\psi$ of the infinite adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, an arbitrary function $S$ on real $2\times 3$ matrices with complex values, and reals $a_1 \neq 0$, $a_2 > 0$. Let $q \in GL_2(\mathbb{R})$ be the upper-unit matrix $\begin{pmatrix} a_1 & 0 \\ 0 & a_2\end{pmatrix}$, let $\hat\iota(q) \in GL_3$ of the infinite adeles be its image under the embedding at the real place of $\mathbb{Q}$, the block embedding $GL_2 \hookrightarrow GL_3$ with last diagonal entry $1$, and the projection to the archimedean component, and let $g = w_3 \cdot {}^t\hat\iota(q)^{-1}$, where $w_3$ is the antidiagonal permutation matrix $!![0,0,1;0,1,0;1,0,0]$ and ${}^t(\cdot)^{-1}$ is `transposeInv3`. Then the Jacquet vector $\mathrm{jacquetVector3}\,D\,u_3\,a_3\,a\,\psi\,S$ at $g$, that is $\chi_{u_3+1,a_3}(\det g) \int_{e} \mathrm{godementInner3}\,\psi\,S\,e\,g \cdot \chi_{u_3+2,a_3}(\det e)\,|\det e|^{-2}\, W(\mathrm{diag}(a,1)\,e^{-1})\,de$ over real $2\times 2$ matrices $e$, with $\chi_{u,b}(y) = |y|^{u}$ times $\mathrm{sign}(y)$ when $b \neq 0$, equals $$\chi_{u_3+1,a_3}\bigl(-(a_1a_2)^{-1}\bigr)\int_{e}\Bigl(\int_{v \in \mathbb{R}^2} S\bigl(e \cdot \begin{smallmatrix} v_0/a_1 & 0 & 1 \\ v_1/a_1 & a_2^{-1} & 0\end{smallmatrix}\bigr)\,\psi(-v_1)\,dv\Bigr)\chi_{u_3+2,a_3}(\det e)\,|\det e|^{-2}\,W(\mathrm{diag}(a,1)\,e^{-1})\,de,$$ where $-v_1$ is embedded in the infinite adeles at the real place.
--
--   This is the explicit evaluation, in the dual Godement configuration, of the $GL_3$ Jacquet vector attached to a section $S$ at the long-Weyl translate of the transpose-inverse of a diagonal Siegel torus point; the quasi-character prefactor records the determinant $-(a_1a_2)^{-1}$ of the resulting real matrix. It is used in the Rankin–Selberg computations of dual torus pairs for explicit Gaussian and harmonic sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    jacquetVector3 D u₃ a₃ a ψ S
        (longWeyl3 * transposeInv3 (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ
          (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
            (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne'))))) =
      ArchR.quasiChar (u₃ + 1) a₃ (-(a₁ * a₂)⁻¹) *
        ∫ e : Fin 2 → Fin 2 → ℝ,
          (∫ v : Fin 2 → ℝ,
              S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
                ψ (AutomorphicForm.StandardKernel.ofReal (-(v 1)))) *
            ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            D.W (ArchR.diagOne a * (Matrix.of e)⁻¹) := by sorry
