-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2
-- name    : LanglandsTunnell.CubicInduction.WhittakerBlock.sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/56b8023a-5343-5001-a537-1205fddb652d
-- title:
--   Reverse-cyclic cubic equals C₃+C₁²-3C₂
-- statement:
--   Fix a function $F$ on $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$ (the group `AdelicGL 3 (𝓞 ℚ) ℚ`, i.e. the general linear group of $3\times 3$ matrices over the adele ring of $\mathbb{Q}$) with complex values, and assume [`WhittakerBlock.IsArchSmooth3 F`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21): for every $g$ the function $e \mapsto F(g\cdot \mathrm{archRealLift3}\,e)$ on real $3\times 3$ matrices $e$ is $C^\infty$ on the open set where $\det e \neq 0$, where $\mathrm{archRealLift3}\,e$ is the element of $\mathrm{GL}_3$ of the adeles obtained from the real matrix $e$ placed at the archimedean place when that matrix is a unit, and is $1$ otherwise. For indices $i,j \in \{0,1,2\}$, $\operatorname{archDeriv} i\, j\, \varphi$ is the right derivative $(\operatorname{archDeriv} i\,j\,\varphi)(g) = \tfrac{d}{ds}\varphi\bigl(g\cdot \mathrm{archRealLift3}(I + sE_{ij})\bigr)\big|_{s=0}$, written $\partial_{ij}$, and $\mathrm{casimir1}\,\varphi = \sum_i \partial_{ii}\varphi$, $\mathrm{casimir2}\,\varphi = \sum_{i,j}\partial_{ij}\partial_{ji}\varphi$, $\mathrm{casimir3}\,\varphi = \sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}\varphi$ (innermost derivative applied first). The assertion is the equality of functions on $\mathrm{GL}_3$ of the adeles $$\sum_{i,j,k}\partial_{ij}\partial_{ki}\partial_{jk}F = \mathrm{casimir3}\,F + \mathrm{casimir1}(\mathrm{casimir1}\,F) - 3\,\mathrm{casimir2}\,F,$$ the scalar $3$ acting as a complex number.
--
--   The degree-three cyclic generator of the centre of $U(\mathfrak{gl}_3)$, realised as a right-invariant differential operator at the archimedean place, is not invariant under reversing the cyclic word $\partial_{ij}\partial_{jk}\partial_{ki} \mapsto \partial_{ij}\partial_{ki}\partial_{jk}$; the identity records that the difference is the central expression $C_1^2 - 3C_2$, and its proof rests on the commutation rule $\partial_{ij}\partial_{kl} - \partial_{kl}\partial_{ij} = \delta_{jk}\partial_{il} - \delta_{li}\partial_{kj}$ packaged in [`LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate`](thm.html#LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate). It is used in the construction of joint Casimir eigenvectors and in the dichotomy for transition-stable families within the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F) :
    (fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDeriv i j (archDeriv k i (archDeriv j k F)) g) =
      casimir3 F + casimir1 (casimir1 F) - (3 : ℂ) • casimir2 F := by sorry
