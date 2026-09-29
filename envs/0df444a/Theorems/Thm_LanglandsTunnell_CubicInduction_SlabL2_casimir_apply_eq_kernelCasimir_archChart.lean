-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart
-- name    : LanglandsTunnell.CubicInduction.SlabL2.casimir_apply_eq_kernelCasimir_archChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/a00e12d1-8144-5b3f-a3ff-a9327ee2f7bd
-- title:
--   Casimir operators through the archimedean chart at the identity
-- statement:
--   Let $F\colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be a function on the group of invertible $3\times 3$ matrices over the adele ring of $\mathbb{Q}$, assume [`WhittakerBlock.IsArchSmooth3 F`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), i.e. for every base point $g$ the map $e\mapsto F(g\cdot\mathtt{archRealLift3}\,e)$ is $C^\infty$ on the set of real arrays $e \colon \mathrm{Fin}\,3\to\mathrm{Fin}\,3\to\mathbb{R}$ with $\det(e)\neq 0$, where $\mathtt{archRealLift3}\,e$ is the unit of the matrix group attached to `archRealMat3 e` when that matrix is invertible and $1$ otherwise, and let $x$ be a point of the group. Write $\beta = \mathtt{archChart}\,F\,x$, $\beta(m)=F(x\cdot\mathtt{archRealLift3}\,m)$, and let $L_{ij}\beta(m)=-(d\beta)_m(E_{ij}m)$, the matrix $E_{ij}m$ having $i$-th row the $j$-th row of $m$ and all other rows zero. The assertion is fourfold, at the real identity array $m=1$: first, $\beta(1)=F(x)$; second, $\sum_i \mathtt{archDeriv}\,i\,i\,F(x) = -\sum_i L_{ii}\beta(1)$; third, $\sum_{i,j}\mathtt{archDeriv}\,i\,j(\mathtt{archDeriv}\,j\,i\,F)(x)=\sum_{i,j}L_{ij}L_{ji}\beta(1)$; fourth, $\sum_{i,j,k}\mathtt{archDeriv}\,i\,j(\mathtt{archDeriv}\,j\,k(\mathtt{archDeriv}\,k\,i\,F))(x) = -\sum_{i,j,k}L_{ki}L_{jk}L_{ij}\beta(1)$. Here $\mathtt{archDeriv}\,i\,j\,\varphi(g)$ is the derivative at $s=0$ of $s\mapsto \varphi(g\cdot\mathtt{archRealLift3}(1+sE_{ij}))$.
--
--   This identifies the degree one, two and three Casimir expressions $\sum E_{ii}$, $\sum E_{ij}E_{ji}$ and $\sum E_{ij}E_{jk}E_{ki}$ of $\mathfrak{gl}_3$, acting on $F$ by iterated right derivatives at the infinite place, with the corresponding left-invariant operators evaluated on the chart $m\mapsto F(x\cdot\mathtt{archRealLift3}\,m)$ at the identity, the third in its transposed ordering. It is used in the reduction of the Casimir eigenvalue condition to a property of smoothing kernels, in `casimir_eq_smul_of_forall_isSmoothingKernel_casimir_smoothingOperator_eq_smul`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.SlabL2.casimir_apply_eq_kernelCasimir_archChart
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archChart F x (fun a b => if a = b then 1 else 0) = F x ∧
      WhittakerBlock.casimir1 F x = -kernelCasimir1 (archChart F x) (fun a b => if a = b then 1 else 0) ∧
        WhittakerBlock.casimir2 F x = kernelCasimir2 (archChart F x) (fun a b => if a = b then 1 else 0) ∧
          WhittakerBlock.casimir3 F x = -kernelCasimir3T (archChart F x) (fun a b => if a = b then 1 else 0) := by sorry
