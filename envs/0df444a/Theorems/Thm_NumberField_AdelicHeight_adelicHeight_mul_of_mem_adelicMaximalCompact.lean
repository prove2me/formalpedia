-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
-- name    : NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/b97efbb2-4700-5805-af1f-3f78a9af2bdd
-- title:
--   Right K-invariance of the adelic height on GL₂
-- statement:
--   Let $F$ be a number field and let $g$ and $k$ be elements of `AdelicGL2 (𝓞 F) F`, the group $\mathrm{GL}_2$ over the adele ring of $F$. Suppose $k$ belongs to the subgroup [`AutomorphicForm.adelicMaximalCompact F`](def/AutomorphicForm_AdelicMaximalCompact.html#L19), that is: the finite part `glFin (𝓞 F) F k` lies in `finiteIntegralGL2 (𝓞 F) F` (the level-zero subgroup `finiteLevelZero (𝓞 F) F ⊤` of $\mathrm{GL}_2$ over the finite adeles), and for every infinite place $w$ of $F$ the $w$-component `archComponent F w (glArch (𝓞 F) F k)` satisfies `IsRowIsometry`, i.e. the norm of its determinant is $1$ and for all $x,y$ in the completion at $w$ one has $\|x k_{00}+y k_{10}\|^2+\|x k_{01}+y k_{11}\|^2=\|x\|^2+\|y\|^2$. The conclusion is that `adelicHeight F (g * k) = adelicHeight F g`, where `adelicHeight F g` is the product of the archimedean height $\prod_{w\mid\infty}\mathrm{localHeight}(\mathrm{archComponent}\,w\,(\mathrm{glArch}\,g))^{w.\mathrm{mult}}$ with the finite height $\prod^{\mathrm{f}}_{v}\mathrm{finLocalHeight}(\mathrm{finComponent}\,v\,(\mathrm{glFin}\,g))$, the latter a multiplicative finite product over the height-one spectrum of $\mathcal O_F$.
--
--   This is the right invariance of the adelic height function under the standard maximal compact subgroup of $\mathrm{GL}_2(\mathbb A_F)$, the property that makes the height descend to the Iwasawa coordinate $t$ and hence makes truncated Siegel sets and windowed Siegel sets well defined. It is used throughout the adelic analytic layer of the development, for instance in the construction of invariant band-supported approximations and in the integral estimates for twisted Bruhat decompositions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact.lean

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicHeight AutomorphicForm

theorem NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact
    (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ AutomorphicForm.adelicMaximalCompact F) :
    adelicHeight F (g * k) = adelicHeight F g := by sorry
