-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_commute_archDeriv_and_sum_reversed_cubic_eq
-- name    : LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_commute_archDeriv_and_sum_reversed_cubic_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/290e8068-ce5c-58a7-9c26-f309ab295386
-- title:
--   Gelfand central operators commute with right derivatives; reversed cubic identity
-- statement:
--   For $i,j$ ranging over $\mathrm{Fin}\,3$, `archDerivₗ i j` is the operator form of `archDeriv i j`, the right derivative at the archimedean place in the direction of the matrix unit $E_{ij}$: it sends a $\mathbb{C}$-valued function $\varphi$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ (the adele ring of $\mathbb{Q}$ built from $\mathcal{O}_{\mathbb{Q}}$) to $g \mapsto \frac{d}{ds}\varphi\bigl(g\cdot \mathrm{archRealLift3}(1 + sE_{ij})\bigr)\big|_{s=0}$, where `archRealLift3` sends a real $3\times 3$ matrix to the corresponding adelic matrix when the latter is a unit and to $1$ otherwise. Products below are taken in the ambient operator algebra, i.e. composition of operators, and the statement carries no hypotheses or free variables. It asserts four things at once: first, that $\sum_i D_{ii}$ commutes with $D_{ab}$ for all $a,b$; second, that $\sum_{i,j} D_{ij}D_{ji}$ commutes with every $D_{ab}$; third, that $\sum_{i,j,k} D_{ij}D_{jk}D_{ki}$ commutes with every $D_{ab}$; and fourth, the identity $$\sum_{i,j,k} D_{ji}D_{kj}D_{ik} = \sum_{i,j,k} D_{ij}D_{jk}D_{ki} + \Bigl(\sum_i D_{ii}\Bigr)^{2} - 3\sum_{i,j} D_{ij}D_{ji},$$ where $D_{ij}$ abbreviates `archDerivₗ i j` and the factor $3$ acts by the $\mathbb{C}$-scalar action.
--
--   The three sums are the operators by which the Gelfand central elements of degrees $1$, $2$ and $3$ of $U(\mathfrak{gl}_3)$ act by right differentiation at the real place, so parts one to three are their centrality and part four rewrites the oppositely ordered cubic sum in terms of them. The result feeds the archimedean smoothness and centre-finiteness steps of the cubic induction, being used by [`LanglandsTunnell.CubicInduction.isArchSmooth3_and_sum_smul_iterate_casimir_eq_zero_of_mem_span_foldr_archDeriv_mul_right`](thm.html#LanglandsTunnell.CubicInduction.isArchSmooth3_and_sum_smul_iterate_casimir_eq_zero_of_mem_span_foldr_archDeriv_mul_right) and [`LanglandsTunnell.CubicInduction.isCentreFinite_comp_transposeInv3_of_isArchSmooth3`](thm.html#LanglandsTunnell.CubicInduction.isCentreFinite_comp_transposeInv3_of_isArchSmooth3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_commute_archDeriv_and_sum_reversed_cubic_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_EnvelopingAction3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_commute_archDeriv_and_sum_reversed_cubic_eq :
    (∀ a b : Fin 3, Commute (∑ i : Fin 3, archDerivₗ i i) (archDerivₗ a b)) ∧
    (∀ a b : Fin 3, Commute (∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * archDerivₗ j i) (archDerivₗ a b)) ∧
    (∀ a b : Fin 3,
      Commute (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ i j * archDerivₗ j k * archDerivₗ k i)
        (archDerivₗ a b)) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ j i * archDerivₗ k j * archDerivₗ i k =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ i j * archDerivₗ j k * archDerivₗ k i) +
        (∑ i : Fin 3, archDerivₗ i i) * (∑ i : Fin 3, archDerivₗ i i) -
        (3 : ℂ) • ∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * archDerivₗ j i) := by sorry
