-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir
-- name    : LanglandsTunnell.CubicInduction.SlabL2.casimir_archConvN_and_eq_of_forall_integral_kernelCasimir
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/0e585a77-ccc2-5fe4-bc9e-cbff8d2ed4ad
-- title:
--   Casimir operators on archimedean convolutions, and weak eigenfunction equations
-- statement:
--   A closed statement asserting the conjunction of two families of claims for $G=\mathrm{GL}_3$ over $\mathbb{Q}$. Throughout, $\mathrm{AdelicGL}\,3\,(\mathcal{O}_{\mathbb{Q}})\,\mathbb{Q}$ is $\mathrm{GL}_3$ of the adele ring, $\mathrm{kernelEnt}$ sends $h \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ to its real $3\times 3$ entry array obtained by applying `StandardKernel.realCoord` entrywise, $\mathrm{archConvN}$ is the integral $g \mapsto \int \Phi(g\cdot \mathrm{archInclN}\,h)\,\alpha(h)\,dh$ against Haar measure `archGLHaarN` on $\mathrm{GL}_3$ of the infinite adeles (with its Borel structure), and `IsSmoothArchFactor β` means that $\beta$ is $C^{\infty}$ on the space of real $3\times 3$ arrays, has compact support, and has $\mathrm{tsupport}\,\beta$ contained in $\{m \mid \det(\mathrm{of}\,m) \neq 0\}$. The operators $\mathrm{kernelCasimir}_1,\mathrm{kernelCasimir}_2,\mathrm{kernelCasimir}_3$ are $\sum_i L_{ii}$, $\sum_{i,j}L_{ij}L_{ji}$, $\sum_{i,j,k}L_{ij}L_{jk}L_{ki}$ and $\mathrm{kernelCasimir3T}$ is $\sum_{i,j,k}L_{ki}L_{jk}L_{ij}$, where $L_{ij}$ denotes the operator `kernelLeftDeriv i j` on complex functions of entry arrays; $\mathrm{WhittakerBlock.casimir}_1,\mathrm{casimir}_2,\mathrm{casimir}_3$ are $\sum_i D_{ii}$, $\sum_{i,j}D_{ij}D_{ji}$, $\sum_{i,j,k}D_{ij}D_{jk}D_{ki}$, where $D_{ij}\varphi(g)$ is the derivative at $s=0$ of $s \mapsto \varphi(g\cdot \mathrm{archRealLift3}(1+sE_{ij}))$. First claim: for every continuous $\Phi : \mathrm{GL}_3(\mathbb{A}) \to \mathbb{C}$ and every $\beta$ satisfying `IsSmoothArchFactor`, the three functions $\mathrm{kernelCasimir}_k\,\beta$ again satisfy `IsSmoothArchFactor`, and for $k=1,2,3$ one has $\mathrm{casimir}_k\big(\mathrm{archConvN}\,\Phi\,(\beta \circ \mathrm{kernelEnt})\big) = \mathrm{archConvN}\,\Phi\,((\mathrm{kernelCasimir}_k\,\beta) \circ \mathrm{kernelEnt})$. Second claim: for every $f$ on real $3\times 3$ arrays and every $c \in \mathbb{C}$, three implications hold. If $f$ is $C^1$ (resp. $C^2$, resp. $C^3$) on $\{m \mid \det(\mathrm{of}\,m)\neq 0\}$ and $\int f(\mathrm{kernelEnt}\,h)\,(\mathrm{kernelCasimir}_k\,\beta)(\mathrm{kernelEnt}\,h)\,dh = c\int f(\mathrm{kernelEnt}\,h)\,\beta(\mathrm{kernelEnt}\,h)\,dh$ for all $\beta$ satisfying `IsSmoothArchFactor`, with $k=1$ (resp. $2$, resp. $3$), then for all $m$ with $\det(\mathrm{of}\,m)\neq 0$ one has $-\mathrm{kernelCasimir}_1 f(m) = c\,f(m)$ (resp. $\mathrm{kernelCasimir}_2 f(m) = c\,f(m)$, resp. $-\mathrm{kernelCasimir3T}\,f(m) = c\,f(m)$), the signs and the reversal of the cubic operator recording the adjointness of $L_{ij}$ with respect to Haar measure.
--
--   This is the archimedean calculus behind the smoothing operator for $\mathrm{GL}_3$ over $\mathbb{Q}$: the right-invariant differential operators of degrees $1,2,3$ acting on an archimedean convolution may be transferred to the kernel, and a function of the matrix entries which is a Casimir eigenfunction in the weak (distributional) sense against all smooth compactly supported kernels supported in the invertible arrays is one in the pointwise sense. It is used in the deduction that the smoothing operators attached to such kernels act on the relevant space by scalars.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction
  LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.SlabL2.casimir_archConvN_and_eq_of_forall_integral_kernelCasimir :
    (∀ (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous Φ → ∀ (β : (Fin 3 → Fin 3 → ℝ) → ℂ), IsSmoothArchFactor β →
      (IsSmoothArchFactor (kernelCasimir1 β) ∧ IsSmoothArchFactor (kernelCasimir2 β) ∧
          IsSmoothArchFactor (kernelCasimir3 β)) ∧
        WhittakerBlock.casimir1 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
            archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir1 β (kernelEnt h)) ∧
          WhittakerBlock.casimir2 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
              archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir2 β (kernelEnt h)) ∧
            WhittakerBlock.casimir3 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
              archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir3 β (kernelEnt h))) ∧
      ∀ (f : (Fin 3 → Fin 3 → ℝ) → ℂ) (c : ℂ),
        (ContDiffOn ℝ 1 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir1 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → -kernelCasimir1 f m = c * f m) ∧
        (ContDiffOn ℝ 2 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir2 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → kernelCasimir2 f m = c * f m) ∧
        (ContDiffOn ℝ 3 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir3 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → -kernelCasimir3T f m = c * f m) := by sorry
