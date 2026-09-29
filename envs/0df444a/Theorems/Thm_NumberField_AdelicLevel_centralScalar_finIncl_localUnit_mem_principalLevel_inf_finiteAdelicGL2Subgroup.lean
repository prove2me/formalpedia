-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup
-- name    : NumberField.AdelicLevel.centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/13643f61-3abf-5002-866c-3079ccbf68e5
-- title:
--   Central unit idele at v ∤ N lies in U(N)
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal{O}_K$, and $v$ a nonzero prime of $\mathcal{O}_K$ (a point of the height-one spectrum) whose underlying ideal `v.asIdeal` does not divide $N$. Let $t$ be a unit of the completion $K_v$ whose valuation $\mathrm{Valued.v}(t)$ equals $1$. Form the finite idele $\mathrm{localUnit}\,v\,t$, which has component $t$ at $v$ and $1$ at every other finite place, push it into the ideles along `finIncl` (the map sending a finite adele $x$ to the adele $(1, x)$ with trivial archimedean component), and let $c = \mathrm{diag}(\hat t, \hat t)$ be its image under [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18), i.e. the scalar matrix in $GL_2(\mathbb{A}_K)$ attached to this idele. The assertion is that $c$ lies in the intersection of `principalLevel (𝓞 K) K N`, which is `levelOne (𝓞 K) K N` (the pullback along the finite-part map `glFin` of the finite level-$N$ subgroup, cut out by the predicate `IsLevelOneMatrix (𝓞 K) K N` on the finite part of a matrix and of its inverse) intersected with the image of that same subgroup under conjugation by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, with [`AutomorphicForm.finiteAdelicGL2Subgroup K`](def/AutomorphicForm_SmoothAutomorphicFnAt.html#L15), the kernel of `glArch` — that is, the matrices whose archimedean component is the identity.
--
--   This is the statement that a central idele supported at a single finite place $v$ away from the level, with unit component there, lies in the principal congruence subgroup of level $N$ of $GL_2(\mathbb{A}_K)$ and has trivial archimedean part. It supplies the invariance used when test functions bi-invariant under the level-$N$ group are integrated over cells, and is cited by [`AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine) and by [`AutomorphicForm.setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one`](thm.html#AutomorphicForm.setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup.lean

import Mathlib
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem NumberField.AdelicLevel.centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ N)
    (t : (v.adicCompletion K)ˣ) (ht : Valued.v (t : v.adicCompletion K) = 1) :
    AutomorphicForm.centralScalar (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) ∈
      principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K := by sorry
