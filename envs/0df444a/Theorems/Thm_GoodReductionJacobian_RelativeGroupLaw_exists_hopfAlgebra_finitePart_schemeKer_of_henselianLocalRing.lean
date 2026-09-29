-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/6ffffaf9-e34d-56c5-b3de-027daeb22987
-- title:
--   Finite part of the n-torsion over a henselian local ring
-- statement:
--   Let $R$ be a henselian local commutative ring, let $f \colon X \to \operatorname{Spec} R$ be separated and locally of finite type, and let $L$ be a relative group law for $f$: a group structure on each set $\{\varphi \colon T \to X \mid \varphi \circ f = t\}$ of sections over a scheme $t \colon T \to \operatorname{Spec} R$, with multiplication, unit and inverse satisfying associativity, the unit laws and left inversion, the multiplication being natural under morphisms $T' \to T$ over $\operatorname{Spec} R$; assume further that all these multiplications are commutative. Fix $n \in \mathbb{N}$ and write $X[n] = \operatorname{Spec} R \times_{X} X$ for the pullback of the endomorphism $\mathrm{n}\colon X \to X$ obtained by iterating $L$ on the identity section against the unit section, with structure morphism $X[n] \to \operatorname{Spec} R$ the second projection; assume this morphism is locally quasi-finite, quasi-compact and flat. Then there exist a commutative $R$-Hopf algebra $H$ in the same universe which is finite and flat as an $R$-module and cocommutative, a morphism $j \colon \operatorname{Spec} H \to X[n]$, and for every commutative $R$-algebra $T$ a map $e_T$ from the convolution monoid of $R$-algebra homomorphisms $H \to T$ to the set of $n$-torsion sections of $f$ over $\operatorname{Spec} T$ (those $x$ with $n x$ equal to the unit), such that: $j$ followed by the structure morphism of $X[n]$ is $\operatorname{Spec}$ of the structure map $R \to H$; $j$ is both an open and a closed immersion; every point of $X[n]$ lying over the closed point of $R$ lies in the image of $j$ on points; for each $T$ and each $\varphi$, the morphism underlying $e_T(\varphi)$ is $\operatorname{Spec} \varphi$ followed by $j$ followed by the first projection $X[n] \to X$; each $e_T$ is injective, and surjective whenever $T$ is finite as an $R$-module; each $e_T$ carries the convolution product $\varphi \psi$ to the product of $e_T(\varphi)$ and $e_T(\psi)$ under $L$; and for $g \colon T \to T'$ an $R$-algebra map, the morphism underlying $e_{T'}(g \circ \varphi)$ is $\operatorname{Spec} g$ followed by that underlying $e_T(\varphi)$.
--
--   This is the construction of the finite part of the quasi-finite separated $R$-scheme $X[n]$ over a henselian local base: the $n$-torsion splits as a finite flat open and closed subgroup, represented by a finite flat cocommutative Hopf algebra $H$ whose points compute $n$-torsion with values in module-finite $R$-algebras, together with all points of the special fibre. It is used downstream in the analysis of torsion of Jacobians with good reduction, for instance in lifting multiplications on torus fibres and in identifying torsion subgroups with Hopf-algebra spectra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) [LocallyQuasiFinite (L.schemeKerStr n)] [QuasiCompact (L.schemeKerStr n)] [Flat (L.schemeKerStr n)] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ (j : Spec (CommRingCat.of H) ⟶ L.schemeKer n)
        (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) → L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n),

        j ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R H)) ∧
        IsOpenImmersion j ∧ IsClosedImmersion j ∧

        (∀ x : ↥(L.schemeKer n), (L.schemeKerStr n).base x = IsLocalRing.closedPoint R → x ∈ Set.range j.base) ∧

        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
          ((e T φ).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ j ≫
              pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T], Function.Injective (e T)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] [Module.Finite R T], Function.Surjective (e T)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) := by sorry
