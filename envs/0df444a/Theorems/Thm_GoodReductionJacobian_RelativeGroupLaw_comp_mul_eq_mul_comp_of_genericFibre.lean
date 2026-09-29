-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
-- name    : GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/22e604ca-b7d3-5efc-95fa-6f4ca04eb3db
-- title:
--   Generic-fibre homomorphism property spreads to all points
-- statement:
--   Let $R$ be a commutative domain and $K$ a field that is a fraction field of $R$ via the given algebra structure, and let $X$, $T$ be schemes equipped with morphisms $f : X \to \operatorname{Spec} R$ and $t : T \to \operatorname{Spec} R$, with $f$ separated and $t$ flat. Suppose given relative group laws $G$ for $f$ and $H$ for $t$: for each scheme $S$ and each $s : S \to \operatorname{Spec} R$ these equip the set of morphisms $S \to X$ (resp. $S \to T$) whose composite with $f$ (resp. $t$) equals $s$ with a multiplication, unit and inversion satisfying the group axioms and natural in $(S,s)$ under precomposition. Let $\varphi : T \to X$ satisfy $\varphi$ followed by $f$ equals $t$. Assume that $\varphi$ is multiplicative on points valued in schemes over $K$: for every scheme $S$ and every $s : S \to \operatorname{Spec} K$, and all $x, y$ over $s$ followed by $\operatorname{Spec}$ of the structure map $R \to K$, the composite of $H$-multiplication of $x,y$ with $\varphi$ equals the $G$-multiplication of $x$ followed by $\varphi$ and $y$ followed by $\varphi$. The conclusion is that this identity holds for every scheme $S$, every $s : S \to \operatorname{Spec} R$ and all such $x, y$.
--
--   This is the standard spreading-out step in the construction of group laws on Néron models and on models of abelian varieties: a morphism over $R$ that is a homomorphism on generic-fibre points is a homomorphism on all points, because a flat source and separated target force equality of two morphisms agreeing over the generic fibre. It is used in the uniqueness of extensions of homomorphisms to abelian schemes and in comparing relative group laws, and further downstream in the analysis of fibres of models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

theorem GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)}
    {t : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)}
    [AlgebraicGeometry.IsSeparated f] [AlgebraicGeometry.Flat t]
    (G : GoodReductionJacobian.RelativeGroupLaw R f) (H : GoodReductionJacobian.RelativeGroupLaw R t)
    (φ : NeronModelInfra.SchemeHomOver t f)
    (hφ : ∀ {S : AlgebraicGeometry.Scheme.{u}} (s : S ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
        (x y : NeronModelInfra.SchemeHomOver (s ≫ NeronModelInfra.specGenericFibreInclusion R K) t),
        (H.mul _ x y).1 ≫ φ.1 =
          (G.mul _ ⟨x.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, x.2]⟩
            ⟨y.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, y.2]⟩).1)
    {S : AlgebraicGeometry.Scheme.{u}} (s : S ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (x y : NeronModelInfra.SchemeHomOver s t) :
    (H.mul s x y).1 ≫ φ.1 =
      (G.mul s ⟨x.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, x.2]⟩
        ⟨y.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, y.2]⟩).1 := by sorry
