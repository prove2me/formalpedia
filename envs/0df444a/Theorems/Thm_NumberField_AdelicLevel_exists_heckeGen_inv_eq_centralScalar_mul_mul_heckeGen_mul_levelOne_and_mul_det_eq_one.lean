-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one
-- name    : NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/55aeb1b7-c7e8-505a-9012-8623793b42c9
-- title:
--   Inverse of the Hecke generator in its level-N double coset
-- statement:
--   Let $L$ be a number field, $N$ an ideal of $\mathcal{O}_L$, and $S$ a finite set of height-one primes of $\mathcal{O}_L$ such that every prime $v$ with $v \mid N$ lies in $S$. The assertion is that for every height-one prime $w$ of $\mathcal{O}_L$ with $w \notin S$ there exist a unit $z$ of the adele ring of $L$ and elements $u_1, u_2$ of $\mathrm{GL}_2$ of the adele ring of $L$, both lying in the intersection of `levelOne`, the pullback along the finite-part map `glFin` of the subgroup of matrices $g$ over the finite adeles with both $g$ and $g^{-1}$ satisfying `IsLevelOneMatrix` for $N$, with `finiteAdelicGL2Subgroup`, the kernel of the archimedean-part map `glArch`, such that, writing $g_w$ for `heckeGen` at $w$, namely the image under `heckeGenAt` (the composite of `localUnit` at $w$, the inclusion `finIncl` of finite-adelic units into adelic units, and `diagOne`) of the uniformiser unit at $w$, one has $g_w^{-1} = \mathrm{diag}(z,z)\, u_1\, g_w\, u_2$, with $\mathrm{diag}(z,z)$ the central scalar attached to $z$, and moreover $z \cdot \det g_w = 1$, i.e. $z = (\det g_w)^{-1}$.
--
--   This records that the Hecke generator at a place $w$ outside $S$ is carried to its own inverse by the level-$N$ double coset at $w$ up to a central scalar, the scalar being forced to be $(\det g_w)^{-1}$; it is the form of the relation used for the behaviour of the Hecke operator at a good place under the adelic pairing. It is cited in the analysis of cusp classes leading to [`AutomorphicForm.table_mem_box_of_mem_cuspClasses_slab`](thm.html#AutomorphicForm.table_mem_box_of_mem_cuspClasses_slab).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one
    (L : Type) [Field L] [NumberField L]
    (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ N → v ∈ S) :
    ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L),
        u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧ u₂ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        (heckeGen (𝓞 L) L w)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L w * u₂ ∧
        z * Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w) = 1 := by sorry
