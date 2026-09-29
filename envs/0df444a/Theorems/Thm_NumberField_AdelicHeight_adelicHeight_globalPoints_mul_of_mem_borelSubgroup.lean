-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
-- name    : NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/0845de35-ff60-51b0-946a-fe8b1e73ac91
-- title:
--   Left invariance of the adelic height under B(F)
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$ (written `AdeleRing (𝓞 F) F`). Let $\gamma \in \mathrm{GL}_2(F)$ lie in [`AutomorphicForm.borelSubgroup F`](def/AutomorphicForm_BorelSubgroup.html#L12), that is, the matrix of $\gamma$ has vanishing entry in row $1$, column $0$ (rows and columns indexed by `Fin 2`, so $\gamma$ is upper triangular), and let $g \in \mathrm{GL}_2(\mathbb{A}_F)$ be arbitrary. Write `globalPoints` for the group homomorphism $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_F)$ obtained by applying the structure map $F \to \mathbb{A}_F$ to each matrix entry. Then the adelic height of $\mathrm{globalPoints}(\gamma)\, g$ equals that of $g$, where the adelic height of an element of $\mathrm{GL}_2(\mathbb{A}_F)$ is the product of its archimedean part, $\prod_{v \mid \infty} \mathrm{localHeight}(\cdot)^{v.\mathrm{mult}}$ over the infinite places of $F$ applied to the image in $\mathrm{GL}_2(\mathbb{A}_{F,\infty})$, with its finite part, the finprod over the height-one primes $v$ of $\mathcal{O}_F$ of $\mathrm{finLocalHeight}$ of the $v$-component of the image in $\mathrm{GL}_2$ of the finite adeles.
--
--   This is the invariance of the adelic height on $\mathrm{GL}_2(\mathbb{A}_F)$ under left translation by the rational upper triangular subgroup $B(F)$, which is what makes the height descend to a function on $B(F) \backslash \mathrm{GL}_2(\mathbb{A}_F)$ as required in reduction theory. It is used in the analysis of Siegel sets, truncation and pseudo-Eisenstein series, and in the twisted Bruhat fibre computations that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup.lean

import Mathlib
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField

theorem NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup
    (F : Type) [Field F] [NumberField F]
    {γ : Matrix.GeneralLinearGroup (Fin 2) F} (hγ : γ ∈ AutomorphicForm.borelSubgroup F)
    (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g)
      = NumberField.AdelicHeight.adelicHeight F g := by sorry
