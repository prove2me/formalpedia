-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
-- name    : NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/b88cdf02-ab17-57b2-aab3-97095daf309d
-- title:
--   Strong approximation for GL₂/ℚ at level N with positivity
-- statement:
--   Let $N$ be a nonzero ideal of the ring of integers of $\mathbb{Q}$, and let $g$ be an element of $\mathrm{GL}_2$ over the adele ring of $\mathbb{Q}$. Then there exists $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ with the following two properties for the product of the adelic image of $\gamma$ (that is, [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), the entrywise application of the structure map $\mathbb{Q} \to \mathbb{A}_\mathbb{Q}$) with $g$. First, that product lies in [`NumberField.AdelicLevel.levelOne`](def/NumberField_AdelicLevel.html#L589) for $N$: its finite part, obtained by applying entrywise the projection of the adeles onto the finite adeles, lies in `finiteLevelOne`, i.e. both the resulting matrix over the finite adele ring and the matrix of its inverse satisfy the predicate `IsLevelOneMatrix` for $N$. Second, for every infinite place $w$ of $\mathbb{Q}$ together with a witness that $w$ is real, the matrix obtained from that product by taking its archimedean part, evaluating it at $w$, and transporting the entries along the ring isomorphism of the completion at a real place with $\mathbb{R}$, lies in `Matrix.GLPos (Fin 2) ℝ`, i.e. has positive determinant.
--
--   This is the strong approximation decomposition $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q}) = \mathrm{GL}_2(\mathbb{Q}) \cdot \bigl(\mathrm{GL}_2(\mathbb{R})^{+} \times K_1(N)\bigr)$ in the form needed to pass between classical modular forms of level $\Gamma_1(N)$ and functions on $\mathrm{GL}_2(\mathbb{Q}) \backslash \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$; nothing is asserted about uniqueness, about the intersection $\mathrm{GL}_2(\mathbb{Q}) \cap (\mathrm{GL}_2(\mathbb{R})^{+} \times K_1(N))$, or about fields other than $\mathbb{Q}$. It is used in the adelic reformulation of weight-one cusp forms and in the comparison of compactness conditions on the level subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g
          ∈ NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ N ∧
        ∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ
                  (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g)))
            ∈ Matrix.GLPos (Fin 2) ℝ := by sorry
