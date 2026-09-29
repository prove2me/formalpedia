-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3
-- name    : LanglandsTunnell.CubicInduction.archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/c9c0970a-ba61-53a1-b91d-b1483c90152c
-- title:
--   Archimedean derivatives of a right translate: conjugation by c(k)
-- statement:
--   Let $\varphi : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ satisfy [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), i.e. for every $g$ the function $e \mapsto \varphi(g \cdot \mathrm{archRealLift3}\,e)$ on $3\times 3$ real arrays is $C^\infty$ on the open set where $\det(e) \neq 0$, where $\mathrm{archRealLift3}\,e$ is the adelic matrix obtained from $e$ placed at the infinite place when it is a unit and $1$ otherwise. Let $k, g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ and $i, j \in \{0,1,2\}$, and write $c = \mathrm{realMat}(\mathrm{archComponent3}\,k) \in M_3(\mathbb{R})$ for the real matrix attached to the archimedean component of $k$ through the coordinate map $\mathbb{A}_{\mathbb{Q},\infty} \to \mathbb{R}$. Here `archDeriv i j ψ g` denotes $\frac{d}{ds}\bigl(\psi(g \cdot \mathrm{archRealLift3}(1 + s E_{ij}))\bigr)\big|_{s=0}$, the derivative along the elementary direction $E_{ij}$ at the identity array. The assertion is $$\mathrm{archDeriv}\,i\,j\,\bigl(x \mapsto \varphi(xk)\bigr)(g) \;=\; \sum_{a=0}^{2}\sum_{b=0}^{2} (c^{-1})_{ai}\, c_{jb}\; \bigl(\mathrm{archDeriv}\,a\,b\,\varphi\bigr)(gk),$$ the real coefficients being viewed in $\mathbb{C}$ and $c^{-1}$ the matrix inverse.
--
--   This is the transformation rule $\partial_{E_{ij}} \circ R_k = R_k \circ \partial_{c^{-1}E_{ij}c}$ for the archimedean directional derivatives under right translation, the concrete coefficient form of the adjoint action of $\mathrm{GL}_3(\mathbb{R})$ on one-parameter elementary directions. It feeds the construction of finite-dimensional spaces of derivatives, being cited by [`LanglandsTunnell.CubicInduction.exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule`](thm.html#LanglandsTunnell.CubicInduction.exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j (fun x => φ (x * k)) g =
      ∑ a : Fin 3, ∑ b : Fin 3,
        (((AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ k))⁻¹ a i *
            AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ k) j b : ℝ) : ℂ) *
          WhittakerBlock.archDeriv a b φ (g * k) := by sorry
