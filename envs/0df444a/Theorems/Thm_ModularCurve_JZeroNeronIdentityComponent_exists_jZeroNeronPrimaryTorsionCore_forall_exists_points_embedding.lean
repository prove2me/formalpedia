-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding
-- name    : ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/13437bfd-eaf9-5d64-8a9b-79f4303171b5
-- title:
--   Eisenstein q-primary Néron torsion core with point embedding
-- statement:
--   Let $p$ and $q$ be primes with $q \neq p$ and with $q$ dividing $|p-1|/\gcd(p-1,12)$, i.e. the numerator of $(p-1)/12$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (the predicate `LiesOverPrime`), and let $N$ be a term of `JZeroNeronIdentityComponent p`, that is, a scheme $G$ with a morphism $g \colon G \to \operatorname{Spec}\mathbb{Z}$ carrying a commutative relative group law $L$, together with a bijection $N.\mathrm{pts}$ from $J_0(p) =$ `JZero p` (the degree-zero divisor class group of the level-$p$ modular function field over $\overline{\mathbb{Q}}$) onto the $\overline{\mathbb{Q}}$-points of $g$, subject to the further conditions recorded in that structure (smoothness, separatedness, local finite type, quasi-compactness, surjectivity, preconnected fibres, additivity and Galois-equivariance of $N.\mathrm{pts}$, extension of Hecke operators, flatness and surjectivity of multiplication by $n>0$, finite index of the integral sections). Then there exists a term $C$ of `JZeroNeronPrimaryTorsionCore p q A hA` — fppf sheaves $\mathcal{J}_m$ on the small fppf site of $\operatorname{Spec}\mathbb{Z}$, flat finite-type Hopf algebras $C.H\,m$ over $\mathbb{Z}$ whose sections recover those sheaves through convolution algebras of $\mathbb{Z}$-algebra maps, a bijection $C.\mathrm{genericPoints}\,m$ from `WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ)` onto `eisensteinPrimaryTorsionBar p q m` (the elements of $J_0(p)$ killed by $q^m$ and annihilated by some power of the Eisenstein maximal ideal of the Hecke algebra), a compatible system of $A$-points, the dévissage short exact sequences and the Eisenstein-localised Kummer rows — such that for every $m$ there is a family $\rho$ which assigns to each commutative $\mathbb{Z}$-algebra $T$ and each $\mathbb{Z}$-algebra map $C.H\,m \to T$ a $T$-point of $g$, namely a morphism $\operatorname{Spec} T \to G$ over $\operatorname{Spec}\mathbb{Z}$, with the four properties: each $\rho\,T$ is injective; for $\sigma \colon T \to T'$ and $\varphi \colon C.H\,m \to T$, the point $\rho\,T'\,(\sigma \circ \varphi)$ is $\operatorname{Spec}(\sigma)$ followed by $\rho\,T\,\varphi$; $\rho\,T$ sends the convolution product of two elements of `WithConv (C.H m →ₐ[ℤ] T)` to their product under $L.\mathrm{mul}$; and on $\overline{\mathbb{Q}}$-points $\rho$ agrees with $N.\mathrm{pts}$ applied to the class $C.\mathrm{genericPoints}\,m\,\varphi$ in $J_0(p)$.
--
--   This is the constructor, out of a Néron identity component of $J_0(p)$ over $\mathbb{Z}$, of the Eisenstein $q$-primary torsion data attached to it, in the style of Mazur's treatment of the Eisenstein projectors on $\mathcal{J}^0[q^m]$ and of the Kummer sequence of $\mathcal{J}^0$; the resulting core comes equipped with a group-law-compatible, Galois-compatible embedding of its functor of points into the points of the Néron identity component. It is used in the study of the reduction of the relevant torsion at a place above $p$, by [`ModularCurve.JZeroNeronIdentityComponentGood.exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL`](thm.html#ModularCurve.JZeroNeronIdentityComponentGood.exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve ValuationSubring

theorem ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (hqn : q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (N : JZeroNeronIdentityComponent p) :
    ∃ C : JZeroNeronPrimaryTorsionCore p q A hA, ∀ m : ℕ,
      ∃ ρ : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
          (C.H m →ₐ[ℤ] T) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) N.g,
        (∀ (T : Type) [CommRing T] [Algebra ℤ T], Function.Injective (ρ T)) ∧
        (∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T'] (σ : T →ₐ[ℤ] T') (φ : C.H m →ₐ[ℤ] T),
          (ρ T' (σ.comp φ)).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ρ T φ).1) ∧
        (∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (C.H m →ₐ[ℤ] T)),
          ρ T (WithConv.ofConv (φ * ψ)) = N.L.mul _ (ρ T (WithConv.ofConv φ)) (ρ T (WithConv.ofConv ψ))) ∧
        (∀ φ : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ),
          (ρ (AlgebraicClosure ℚ) (WithConv.ofConv φ)).1
            = (N.pts ((C.genericPoints m φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)).1) := by sorry
