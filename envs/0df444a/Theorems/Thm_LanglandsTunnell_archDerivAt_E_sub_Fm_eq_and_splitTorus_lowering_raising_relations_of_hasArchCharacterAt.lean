-- Prove2me | Theorems.Thm_LanglandsTunnell_archDerivAt_E_sub_Fm_eq_and_splitTorus_lowering_raising_relations_of_hasArchCharacterAt
-- name    : LanglandsTunnell.archDerivAt_E_sub_Fm_eq_and_splitTorus_lowering_raising_relations_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/b94f818f-3a47-55f4-a8d1-c4b4eb15656f
-- title:
--   Weight, lowering and raising relations in torus coordinates
-- statement:
--   Let $F$ be a number field, $w$ a real infinite place of $F$ (witnessed by `hw`), and $W$ a complex-valued function on $GL_2(\mathbb{A}_F)$ (that is, on `AdelicGL2 (𝓞 F) F`). Assume: `IsArchSmoothAt hw W`, i.e. for every $g$ the map $e\mapsto W(g\cdot\mathtt{archRealLiftAt}\ hw\ e)$ is $C^\infty$ on the set of $2\times 2$ real matrices of nonzero determinant; for an integer $k$, the condition `HasArchCharacterAt₀ F w (archWeightCharAt hw k) W`, expressing that right translation of $W$ by the relevant archimedean subgroup at $w$ multiplies it by the character `archWeightCharAt hw k`, the $k$-th power of `archWeightOneAt hw`; and the Whittaker covariance $W(\mathtt{archRealGLAt}\ hw\,(n(x))\cdot p)=e^{2\pi i x}W(p)$ for all $x\in\mathbb{R}$ and all $p$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Write $D_d W(g)$ for `archDerivAt hw d W g`, the derivative at $t=0$ of $t\mapsto W(g\cdot\mathtt{archFlowAt}\ hw\ d\ t)$, for $d\in\{H,E,F^-\}$, and for $y>0$ put $f_g(y)=W(\mathtt{archRealGLAt}\ hw\,(\operatorname{diag}(\sqrt y,1/\sqrt y))\cdot g)$ and $f_{J,g}(y)=W(\mathtt{archRealGLAt}\ hw\,(\mathtt{UpperHalfPlane.J}\cdot\operatorname{diag}(\sqrt y,1/\sqrt y))\cdot g)$, using `splitTorusGL2 (Real.log y / 2)` $=\operatorname{diag}(e^{\log y/2},e^{-\log y/2})$. Then three assertions hold. First, $D_EW(g)-D_{F^-}W(g)=ki\,W(g)$ for every $g$. Second, if $D_HW-i(D_EW+D_{F^-}W)$ vanishes identically, then for every $g$ in `finiteAdelicGL2Subgroup F` (the kernel of `glArch`, i.e. trivial archimedean component): if $f_g$ is differentiable on $(0,\infty)$ then $2yf_g'(y)+(4\pi y-k)f_g(y)=0$ for all $y>0$, and if $f_{J,g}$ is differentiable on $(0,\infty)$ then $2yf_{J,g}'(y)-(4\pi y+k)f_{J,g}(y)=0$ for all $y>0$. Third, if $D_{F^-}W=D_EW$ identically, then for every such $g$ and every $y>0$: differentiability of $f_g$ at $y$ gives $\bigl(D_HW+i(D_EW+D_{F^-}W)\bigr)$ evaluated at $\mathtt{archRealGLAt}\ hw\,(\operatorname{diag}(\sqrt y,1/\sqrt y))\cdot g$ equal to $2yf_g'(y)-4\pi y f_g(y)$, and differentiability of $f_{J,g}$ at $y$ gives the same expression evaluated at $\mathtt{archRealGLAt}\ hw\,(\mathtt{UpperHalfPlane.J}\cdot\operatorname{diag}(\sqrt y,1/\sqrt y))\cdot g$ equal to $2yf_{J,g}'(y)-4\pi(-y)f_{J,g}(y)$.
--
--   These are the Iwasawa-coordinate formulas for the action of $\mathfrak{gl}_2(\mathbb{R})$ at a real place on a function of fixed rotation type with Whittaker covariance under the real unipotent subgroup: the weight relation, the first-order differential equation forced by annihilation under the lowering operator, and the torus-coordinate expression of the raising operator on a weight-zero vector. They are used to obtain the Whittaker factorisations of archimedean Casimir eigenvectors of minimal weight and of weight zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_archDerivAt_E_sub_Fm_eq_and_splitTorus_lowering_raising_relations_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem LanglandsTunnell.archDerivAt_E_sub_Fm_eq_and_splitTorus_lowering_raising_relations_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (W : AdelicGL2 (𝓞 F) F → ℂ) (hWsm : IsArchSmoothAt hw W) (k : ℤ)
    (hWk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) W)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p) :

    (∀ g : AdelicGL2 (𝓞 F) F,
      archDerivAt hw ArchDir.E W g - archDerivAt hw ArchDir.Fm W g = (k : ℂ) * Complex.I * W g) ∧

    ((∀ p : AdelicGL2 (𝓞 F) F,
        archDerivAt hw ArchDir.H W p
          - Complex.I * (archDerivAt hw ArchDir.E W p + archDerivAt hw ArchDir.Fm W p) = 0) →
      ∀ g : AdelicGL2 (𝓞 F) F, g ∈ finiteAdelicGL2Subgroup F →
        (DifferentiableOn ℝ (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) (Set.Ioi 0) →
          ∀ y : ℝ, 0 < y →
            2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) y
              + (4 * (Real.pi : ℂ) * (y : ℂ) - (k : ℂ))
                  * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
        (DifferentiableOn ℝ
            (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) (Set.Ioi 0) →
          ∀ y : ℝ, 0 < y →
            2 * (y : ℂ) * deriv
                (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y
              - (4 * (Real.pi : ℂ) * (y : ℂ) + (k : ℂ))
                  * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0)) ∧

    ((∀ p : AdelicGL2 (𝓞 F) F, archDerivAt hw ArchDir.Fm W p = archDerivAt hw ArchDir.E W p) →
      ∀ g : AdelicGL2 (𝓞 F) F, g ∈ finiteAdelicGL2Subgroup F → ∀ y : ℝ, 0 < y →
        (DifferentiableAt ℝ (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) y →
          archDerivAt hw ArchDir.H W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
              + Complex.I * (archDerivAt hw ArchDir.E W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
                + archDerivAt hw ArchDir.Fm W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))
            = 2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) y
                - 4 * (Real.pi : ℂ) * (y : ℂ) * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) ∧
        (DifferentiableAt ℝ
            (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y →
          archDerivAt hw ArchDir.H W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)
              + Complex.I
                * (archDerivAt hw ArchDir.E W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)
                  + archDerivAt hw ArchDir.Fm W
                      (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))
            = 2 * (y : ℂ) * deriv
                  (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y
                - 4 * (Real.pi : ℂ) * ((-1 * y : ℝ) : ℂ)
                    * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) := by sorry
