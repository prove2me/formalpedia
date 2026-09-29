-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_one
-- name    : ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/d9a61001-963d-5f1a-8bdd-2b08d2db0a81
-- title:
--   Unit point of a relative group law extends to a place
-- statement:
--   Fix a natural number $p$ and write $\mathrm{baseRing}\,p$ for the subring of $\mathbf{Q}$ consisting of rationals whose denominator is coprime to $p$ (for prime $p$, the localisation $\mathbf{Z}_{(p)}$), and $\mathrm{base}\,p = \operatorname{Spec}(\mathrm{baseRing}\,p)$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` and let $\sigma_A : \operatorname{Spec} A \to \mathrm{base}\,p$ be a morphism of schemes, assumed compatible with the generic point in the sense that $\operatorname{Spec}$ of the inclusion $A \hookrightarrow \overline{\mathbf{Q}}$ followed by $\sigma_A$ equals $\mathrm{genPt}\,p$, the morphism $\operatorname{Spec}\overline{\mathbf{Q}} \to \mathrm{base}\,p$ induced by the structure map $\mathrm{baseRing}\,p \to \overline{\mathbf{Q}}$. Let $f : X \to \mathrm{base}\,p$ be a morphism of schemes equipped with a relative group law $L$ in the sense of `RelativeGroupLaw`: functorial multiplication, unit and inverse on the sets of $T$-points of $f$ over each test morphism $t : T \to \mathrm{base}\,p$, satisfying the group axioms and naturality in $T$. The conclusion is that the unit point $L.\mathrm{one}(\mathrm{genPt}\,p)$ satisfies `ExtendsToPlace A σA`; precisely: there exists a point $s : \operatorname{Spec} A \to X$ with $s$ followed by $f$ equal to $\sigma_A$, such that the unit $\overline{\mathbf{Q}}$-point factors as $\operatorname{Spec}(A \hookrightarrow \overline{\mathbf{Q}})$ followed by $s$.
--
--   This records that the unit section of a relative group law is defined integrally at every place: the identity of the group of $\overline{\mathbf{Q}}$-points lies in the subgroup of points extending to $A$-points over $\sigma_A$. Together with the corresponding statements for products and inverses it is used in the study of the models [`ModularCurve.XHDRModelAtP`](def/ModularCurve_XHDRModelAtP.html#L81), in [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero) and [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_one.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.one
    {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ)) (σA : Spec (CommRingCat.of ↥A) ⟶ base p)
    (hσA : barPt A ≫ σA = genPt p)
    {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f) :
    ExtendsToPlace A σA (L.one (genPt p)) := by sorry
