-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat
-- name    : NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/20d4683e-9fc8-5c97-8a02-f3d1c15b5e8a
-- title:
--   Every finite adelic GL₂ matrix over ℚ is globally integralisable
-- statement:
--   Work with the number field $\mathbb{Q}$, its ring of integers $R=\mathtt{NumberField.RingOfIntegers }\mathbb{Q}$ (the Mathlib ring of integers of $\mathbb{Q}$, not the literal $\mathbb{Z}$) and the associated finite adele ring $\mathbb{A}^f=\mathtt{IsDedekindDomain.FiniteAdeleRing } R\ \mathbb{Q}$. The assertion is: for every $g$ in the general linear group $\mathrm{GL}_2(\mathbb{A}^f)$ of $2\times 2$ matrices indexed by `Fin 2`, there exists $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ such that the product of $g$ with the finite adelic image of $\gamma$ lies in the subgroup [`NumberField.AdelicLevel.finiteIntegralGL2`](def/NumberField_AdelicLevel.html#L443). Here the image of $\gamma$ is formed in two steps: [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) sends $\gamma$ to the element of $\mathrm{GL}_2$ of the full adele ring obtained by applying $\operatorname{algebraMap}$ from $\mathbb{Q}$ to the adele ring entrywise, and [`NumberField.AdelicLevel.glFin`](def/NumberField_AdelicLevel.html#L194) then applies entrywise the ring homomorphism `adeleFin` projecting an adele onto its finite component, giving an element of $\mathrm{GL}_2(\mathbb{A}^f)$; the product is taken in that order, the image of $\gamma$ on the left and $g$ on the right. The target subgroup is `finiteLevelZero` at the ideal $\top$, i.e. the group of those $h \in \mathrm{GL}_2(\mathbb{A}^f)$ for which both the matrix underlying $h$ and the matrix underlying $h^{-1}$ satisfy the predicate `IsLevelZeroMatrix` for the ideal $\top$.
--
--   This is the class-number-one statement for $\mathrm{GL}_2$ over $\mathbb{Q}$: the double coset space $\mathrm{GL}_2(\mathbb{Q}) \backslash \mathrm{GL}_2(\mathbb{A}^f) / \mathrm{GL}_2(\widehat{\mathbb{Z}})$ reduces to a single point, so that every finite adelic matrix can be moved into the standard integral subgroup by a rational matrix. It supports the reduction of adelic automorphic forms on $\mathrm{GL}_2$ to classical modular forms, and is used in the construction of Siegel coverings modulo the centre, in the analysis of level-invariant vectors in cuspidal constituents, and in the Hecke coset computations for isotypic cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ) * g
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers ℚ) ℚ := by sorry
