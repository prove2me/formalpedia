-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_mul
-- name    : ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/b8069c6d-3e3e-5633-942e-874d02b77a23
-- title:
--   Extendable points are closed under the relative group law
-- statement:
--   Fix a natural number $p$ and write $\mathbb{Z}_{(p)}$ for the subring `baseRing p` of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$, with base scheme `base p` $=\operatorname{Spec}\mathbb{Z}_{(p)}$; let `genPt p` be the morphism $\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec}\mathbb{Z}_{(p)}$ induced by the structure map. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let `barPt A` be the morphism $\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec} A$ induced by the inclusion $A\hookrightarrow\overline{\mathbb{Q}}$, and let $\sigma_A\colon\operatorname{Spec} A\to\operatorname{Spec}\mathbb{Z}_{(p)}$ be a morphism such that `barPt A` followed by $\sigma_A$ equals `genPt p`. Let $f\colon X\to\operatorname{Spec}\mathbb{Z}_{(p)}$ be a scheme over the base, equipped with a `RelativeGroupLaw`: a functorial group structure on the sets $\{\varphi : T\to X \mid \varphi \text{ followed by } f = t\}$ of $T$-points over each $t\colon T\to\operatorname{Spec}\mathbb{Z}_{(p)}$, natural in the test scheme. Let $x,y$ be points of $X$ over `genPt p`, and suppose each satisfies `ExtendsToPlace A σA`, i.e. each is of the form `barPt A` followed by some point of $X$ over $\sigma_A$. Then the product $L.\mathrm{mul}$ of $x$ and $y$, formed over `genPt p`, again satisfies `ExtendsToPlace A σA`.
--
--   This is the multiplicative half of the assertion that the $\overline{\mathbb{Q}}$-points of $X$ which extend to $A$-points form a subgroup for the relative group law, the elementary part of the Néron mapping property used when reducing points along a place. It is invoked in the study of the Néron-type object attached to $J_0$ at $p$, in the proofs that points coming from explicit degree-zero divisor classes, and differences of Galois translates for elements of inertia, extend over $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.ExtendsToPlace.mul
    {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ)) (σA : Spec (CommRingCat.of ↥A) ⟶ base p)
    (hσA : barPt A ≫ σA = genPt p)
    {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f)
    (x y : SchemeHomOver (genPt p) f)
    (hx : ExtendsToPlace A σA x) (hy : ExtendsToPlace A σA y) :
    ExtendsToPlace A σA (L.mul (genPt p) x y) := by sorry
