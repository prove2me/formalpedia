-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_inv
-- name    : ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/9615d760-68a8-59c3-a465-7571ba648d1f
-- title:
--   Extendability over a valuation ring is closed under inversion
-- statement:
--   Let $p$ be a natural number and write $R_p$ for the subring of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $p$, with $B = \operatorname{Spec} R_p$; let $\mathrm{genPt}\,p \colon \operatorname{Spec}\overline{\mathbf{Q}} \to B$ be induced by the structure map $R_p \to \overline{\mathbf{Q}}$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$, let $\mathrm{barPt}\,A \colon \operatorname{Spec}\overline{\mathbf{Q}} \to \operatorname{Spec} A$ be induced by the inclusion $A \hookrightarrow \overline{\mathbf{Q}}$, and let $\sigma_A \colon \operatorname{Spec} A \to B$ be a morphism such that $\mathrm{barPt}\,A$ followed by $\sigma_A$ equals $\mathrm{genPt}\,p$. Let $f \colon X \to B$ be a scheme over $B$ and let $L$ be a relative group law on $f$, that is, functorial group operations on the sets $\{\varphi \colon T \to X \mid \varphi \text{ followed by } f = t\}$ of sections over each $t \colon T \to B$, with associativity, unit, left inverse and naturality of multiplication. Let $x$ be a section of $f$ over $\mathrm{genPt}\,p$ which satisfies `ExtendsToPlace`, i.e. there is a section $s$ of $f$ over $\sigma_A$ with $x = \mathrm{barPt}\,A$ followed by $s$. Then the inverse $L.\mathrm{inv}\,(\mathrm{genPt}\,p)\,x$ again satisfies `ExtendsToPlace` for $A$ and $\sigma_A$.
--
--   This is the closure of the set of $\overline{\mathbf{Q}}$-points extending to $A$-points under inversion for a relative group law, the companion of the corresponding statements for products and for the unit section. It is used in the construction of the degree-zero divisor classes on modular curves that extend over a place, notably in [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_of_forall_sum_filter_eq_zero) and [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_inv.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.inv
    {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ)) (σA : Spec (CommRingCat.of ↥A) ⟶ base p)
    (hσA : barPt A ≫ σA = genPt p)
    {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f)
    (x : SchemeHomOver (genPt p) f) (hx : ExtendsToPlace A σA x) :
    ExtendsToPlace A σA (L.inv (genPt p) x) := by sorry
