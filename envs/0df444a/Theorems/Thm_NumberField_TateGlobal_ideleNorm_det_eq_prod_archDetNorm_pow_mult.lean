-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
-- name    : NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/d71ae0da-4904-5c1d-a347-609375166150
-- title:
--   Idele norm of det X for integral finite part
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and let $X$ be an element of `AdelicGL2 (𝓞 F) F`, that is of $\mathrm{GL}_2$ over the adele ring of $F$. Assume that the finite part of $X$, its image `glFin (𝓞 F) F X` in $\mathrm{GL}_2$ over the finite adele ring under the entrywise map induced by the projection `adeleFin`, lies in the subgroup `finiteIntegralGL2 (𝓞 F) F`, i.e. in `finiteLevelZero` taken at the level ideal $\top = (1)$: both that matrix and its inverse satisfy the predicate `IsLevelZeroMatrix` at level $(1)$. Then the idele norm of the determinant of $X$ — by definition the real number attached to the value of `MeasureTheory.distribHaarChar` of the additive group of adeles at the unit $\det X$ of the adele ring, i.e. the factor by which multiplication by $\det X$ scales additive Haar measure — equals $\prod_{w} \mathrm{archDetNorm}\,w\,X^{\,w.\mathrm{mult}}$, the product over all infinite places $w$ of $F$ of the norm, in the completion $F_w$, of the determinant of the $w$-component of the archimedean part of $X$, raised to the local degree $[F_w:\mathbb{R}]$.
--
--   This is the statement that an idele whose finite components are determinants of matrices integral at every finite place has idele norm concentrated at the archimedean places, so that the modulus of $\det X$ reduces to the product of the local archimedean absolute values of $\det X_w$ with their multiplicities. It serves as the normalisation computation underlying volume and growth estimates for adelic $\mathrm{GL}_2$ in the analytic part of the development, and is cited throughout the treatment of class sums, cuspidal spectra and windowed Siegel-type arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm

theorem NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (F : Type) [Field F] [NumberField F]
    (X : AdelicGL2 (𝓞 F) F) (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det X) = ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult := by sorry
