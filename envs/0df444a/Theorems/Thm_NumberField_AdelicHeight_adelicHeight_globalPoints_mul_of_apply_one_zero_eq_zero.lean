-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
-- name    : NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/48891325-1d7f-5c29-b97d-461b82762fbd
-- title:
--   Upper-triangular global matrices preserve the adelic height
-- statement:
--   Let $F$ be a number field, let $\gamma$ be an element of $\mathrm{GL}_2(F)$ whose underlying matrix has vanishing $(1,0)$ entry, i.e. $\gamma$ is upper triangular, and let $h$ be an element of $\mathrm{GL}_2(\mathbb{A}_F)$, the general linear group of degree $2$ over the adele ring of $F$ relative to $\mathcal{O}_F$. Write $\mathrm{globalPoints}$ for the group homomorphism $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_F)$ obtained by applying the structure map $F\to\mathbb{A}_F$ entrywise, and let $\mathrm{adelicHeight}$ be the function on $\mathrm{GL}_2(\mathbb{A}_F)$ given by the product of two factors: the archimedean factor $\prod_{v\mid\infty}\mathrm{localHeight}(g_v)^{\,\mathrm{mult}(v)}$, taken over the infinite places of $F$ and applied to the components of the image of $g$ in $\mathrm{GL}_2$ of the infinite adeles, and the finite factor, the finitary product over the height one primes $v$ of $\mathcal{O}_F$ of $\mathrm{finLocalHeight}$ of the $v$-component of the image of $g$ in $\mathrm{GL}_2$ of the finite adele ring. The assertion is that $\mathrm{adelicHeight}_F(\mathrm{globalPoints}(\gamma)\cdot h)=\mathrm{adelicHeight}_F(h)$.
--
--   This is the invariance of the global adelic height under left multiplication by the rational Borel subgroup of $\mathrm{GL}_2(F)$; unlike its archimedean factor alone, the full height is unchanged because the contribution $\prod_v\|\gamma_{00}/\gamma_{11}\|_v$ is trivial by the product formula. It underlies the height estimates for windowed Siegel sets and pseudo-Eisenstein series, and is used in the twisted Bruhat decomposition computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

theorem NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
    (F : Type) [Field F] [NumberField F]
    (γ : GL (Fin 2) F) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (h : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (globalPoints (𝓞 F) F γ * h) = adelicHeight F h := by sorry
