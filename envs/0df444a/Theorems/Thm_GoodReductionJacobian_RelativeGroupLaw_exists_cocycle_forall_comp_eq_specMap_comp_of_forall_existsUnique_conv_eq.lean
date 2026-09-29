-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/6ac853fd-430d-563e-943d-327e1986c9bf
-- title:
--   Difference cocycle from a points-torsor condition
-- statement:
--   Let $R$ be a commutative ring, let $g_N : N \to \operatorname{Spec} R$ be a scheme over $R$ and let $L$ be a relative group law on $g_N$, i.e. a functorial group structure on the sets $\{\varphi : T \to N \mid \varphi \circ g_N = t\}$ of $T$-points over $\operatorname{Spec} R$, compatible with base change along morphisms of bases. Let $H$ and $H_W$ be commutative $R$-bialgebras, $\pi : H \to H_W$ a homomorphism of $R$-bialgebras, $P$ a commutative $R$-algebra and $q_a : H \to P$ an $R$-algebra homomorphism. Assume the points-torsor hypothesis: for every commutative $R$-algebra $C$ and all $R$-algebra maps $a, b : P \to C$ there is a unique $R$-algebra map $c : H_W \to C$ with $a \circ q_a = (c \circ \pi) \ast (b \circ q_a)$, the product being convolution in the monoid of $R$-linear maps $H \to C$. Let $u : \operatorname{Spec} H_W \to N$ be a morphism over $\operatorname{Spec} R$ which is multiplicative on affine points: for every commutative $R$-algebra $C$, all $\varphi, \psi : H_W \to C$ and all $C$-points $x, y$ of $N$ over $\operatorname{Spec} R$ with $x = \operatorname{Spec}(\varphi)$ followed by $u$ and $y = \operatorname{Spec}(\psi)$ followed by $u$, the $L$-product of $x$ and $y$ equals $\operatorname{Spec}(\varphi \ast \psi)$ followed by $u$, where $\varphi \ast \psi$ is the convolution product of $\varphi$ and $\psi$. Finally let $q : \operatorname{Spec} P \to \operatorname{Spec} R$ be the structure morphism. Then there exists a morphism $g$ from $\operatorname{Spec} P \times_{\operatorname{Spec} R} \operatorname{Spec} P$ to $N$ over $\operatorname{Spec} R$ such that, on the triple fibre product formed from the second projection and the first projection of $q$ with itself, the $L$-product of the pullback of $g$ along the first and along the second structural projection equals the pullback of $g$ along the morphism $(\mathrm{pr}_1 \circ \mathrm{pr}_1, \mathrm{pr}_2 \circ \mathrm{pr}_2)$ into the double product — in the classical notation $\mathrm{pr}_{12}^{*} g \cdot \mathrm{pr}_{23}^{*} g = \mathrm{pr}_{13}^{*} g$ — and such that for every commutative $R$-algebra $C$, all $a, b : P \to C$ and $c : H_W \to C$ with $a \circ q_a = (c \circ \pi) \ast (b \circ q_a)$, and every morphism $ab : \operatorname{Spec} C \to \operatorname{Spec} P \times_{\operatorname{Spec} R} \operatorname{Spec} P$ whose two projections are $\operatorname{Spec}(a)$ and $\operatorname{Spec}(b)$, the composite of $ab$ with $g$ equals $\operatorname{Spec}(c)$ followed by $u$.
--
--   This produces the scheme-level difference cocycle $g(a,b) = u(ab^{-1})$ attached to a coset $\operatorname{Spec} P$ under the affine group scheme $\operatorname{Spec} H_W$, together with the compatibility identifying its values on $C$-points with the unique torsor difference $c$; the group law $L$ on $N$ plays the role of the ambient group in which the cocycle is taken. It is used in the construction of a Néron-type extension for the Jacobian of $X_0(N)$, being cited by [`ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_isFinite_forall_ptsN_comp_eq_of_hopf`](thm.html#ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_isFinite_forall_ptsN_comp_eq_of_hopf), where the cocycle is the input to a descent of a trivialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (H : Type) [CommRing H] [Bialgebra R H]
    (H_W : Type) [CommRing H_W] [Bialgebra R H_W] (π : H →ₐc[R] H_W)
    (P : Type) [CommRing P] [Algebra R P] (qa : H →ₐ[R] P)
    (htors : ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C),
      ∃! c : H_W →ₐ[R] C,
        WithConv.toConv (a.comp qa) =
          WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa))
    (u : Spec (CommRingCat.of H_W) ⟶ N) (hu : u ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R H_W)))
    (hmul : ∀ (C : Type) [CommRing C] [Algebra R C] (φ ψ : H_W →ₐ[R] C)
        (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R C))) gN),
      x.1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ u →
      y.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ u →
      (L.mul _ x y).1 =
        Spec.map (CommRingCat.ofHom (WithConv.ofConv (WithConv.toConv φ * WithConv.toConv ψ)).toRingHom) ≫ u)
    (q : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    ∃ g : SchemeHomOver (pullback.fst q q ≫ q) gN,
      L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g ∧
      ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C) (c : H_W →ₐ[R] C),
        WithConv.toConv (a.comp qa) =
          WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa) →
        ∀ ab : Spec (CommRingCat.of C) ⟶ pullback q q,
          ab ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom a.toRingHom) →
          ab ≫ pullback.snd q q = Spec.map (CommRingCat.ofHom b.toRingHom) →
          ab ≫ g.1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u := by sorry
