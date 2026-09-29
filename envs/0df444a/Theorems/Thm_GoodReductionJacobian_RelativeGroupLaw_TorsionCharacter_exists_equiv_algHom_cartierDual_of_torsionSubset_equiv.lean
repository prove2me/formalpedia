-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv
-- name    : GoodReductionJacobian.RelativeGroupLaw.TorsionCharacter.exists_equiv_algHom_cartierDual_of_torsionSubset_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/53ea1fdb-5538-5343-ad36-0770639b3921
-- title:
--   Torsion characters as points of the Cartier dual
-- statement:
--   Let $S$ be a commutative ring, $f \colon A \to \operatorname{Spec} S$ a morphism of schemes, $L$ a relative group law on $f$ (a group structure, functorial under base change, on the sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for every $t \colon T \to \operatorname{Spec} S$), $n$ a natural number, and $\iota \colon \operatorname{Spec} R \to \operatorname{Spec} S$ a morphism with $R$ a commutative ring. Let $H$ be a commutative Hopf $R$-algebra which is finite and free as an $R$-module and whose comultiplication is cocommutative. Assume given, for every commutative $R$-algebra $T$, a bijection $e_T$ from `WithConv (H →ₐ[R] T)`, the $R$-algebra homomorphisms $H \to T$ with their convolution monoid structure, onto the set of $x$ in the fibre of $f$ over $\operatorname{Spec}(\mathrm{algebraMap}\,R\,T)$ followed by $\iota$ with $n \cdot x$ equal to the unit of $L$; assume $e_T$ carries the convolution product to $L.\mathrm{mul}$, and assume naturality: for an $R$-algebra map $g \colon T \to T'$, the scheme morphism underlying $e_{T'}(g \circ \varphi)$ is $\operatorname{Spec} g$ followed by that underlying $e_T(\varphi)$. The conclusion asserts the existence of a family of bijections $\Psi_{R'}$, for $R'$ a commutative $R$-algebra, from the torsion characters of $L$ of order $n$ over $\operatorname{Spec}(\mathrm{algebraMap}\,R\,R')$ followed by $\iota$ (compatible families of unit values $\chi(x) \in T^\times$ on $n$-torsion sections over test rings $T$, multiplicative in $x$ and natural in $T$) onto $\operatorname{Hom}_{R\text{-alg}}(\operatorname{CartierDual} R\,H, R')$, where $\operatorname{CartierDual} R\,H = \operatorname{Hom}_R(H,R)$, with three compatibilities: (i) if $g \colon R' \to R''$ is an $R$-algebra map and $\chi''$, $\chi'$ are characters over $R''$, $R'$ such that $\chi''$ agrees with $\chi'$ on every pair of torsion sections having the same underlying morphism (over a test ring $T$ with $\kappa'' \colon \operatorname{Spec} T \to \operatorname{Spec} R''$, comparing $\chi''$ at $\kappa''$ with $\chi'$ at $\kappa''$ followed by $\operatorname{Spec} g$), then $\Psi_{R''}(\chi'') = g \circ \Psi_{R'}(\chi')$; (ii) if the values of $\chi_3$ are pointwise the product of those of $\chi_1$ and $\chi_2$, then $\Psi_{R'}(\chi_3)$ is the convolution product of $\Psi_{R'}(\chi_1)$ and $\Psi_{R'}(\chi_2)$; (iii) if $\chi$ takes the value $1$ at every torsion section, then $\Psi_{R'}(\chi)$ is the convolution unit.
--
--   This is the Cartier-duality identification, in Yoneda form, of the characters of the $n$-torsion of $A$ over $R'$ with the $R'$-points of the Cartier dual of the Hopf algebra representing that torsion: under the hypothesis that the $n$-torsion of the relative group law is represented by the finite free Hopf $R$-algebra $H$, the character functor is represented by $\operatorname{Hom}_R(H,R)$, compatibly with base change along $R$-algebra maps and with the group structures. It feeds the construction of the admissible-class functor for abelian schemes over a local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.TorsionCharacter.exists_equiv_algHom_cartierDual_of_torsionSubset_equiv
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (n : ℕ)
    {R : Type u} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (H : Type u) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv (H →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ ι) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
      ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) :
    ∃ Ψ : ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
        L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι) ≃ (CartierDual R H →ₐ[R] R'),

      (∀ (R' R'' : Type u) [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R''] (g : R' →ₐ[R] R'')
          (χ' : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
          (χ'' : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ'' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R''))
              (x'' : SchemeHomOver (κ'' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι)) f)
              (hx'' : L.IsTorsionPoint _ n x'')
              (x' : SchemeHomOver ((κ'' ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) ≫
                (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx' : L.IsTorsionPoint _ n x'),
              x''.1 = x'.1 →
                χ''.val T κ'' x'' hx'' = χ'.val T (κ'' ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) x' hx') →
          Ψ R'' χ'' = g.comp (Ψ R' χ')) ∧

      (∀ (R' : Type u) [CommRing R'] [Algebra R R']
          (χ₁ χ₂ χ₃ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
              (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx : L.IsTorsionPoint _ n x),
              χ₃.val T κ x hx = χ₁.val T κ x hx * χ₂.val T κ x hx) →
          Ψ R' χ₃ = (WithConv.toConv (Ψ R' χ₁) * WithConv.toConv (Ψ R' χ₂)).ofConv) ∧
      (∀ (R' : Type u) [CommRing R'] [Algebra R R']
          (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
              (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx : L.IsTorsionPoint _ n x), χ.val T κ x hx = 1) →
          Ψ R' χ = (1 : WithConv (CartierDual R H →ₐ[R] R')).ofConv) := by sorry
