-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero
-- name    : GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_sqZero_of_natCast_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/24965628-8b07-5479-8563-13a020864e1b
-- title:
--   Square-zero deformations of the unit are killed by ℓ
-- statement:
--   Let $R_0$ be a commutative ring, let $A$ be a scheme and let $f \colon A \to \operatorname{Spec} R_0$ be a morphism, and let $G$ be a relative group law on $f$, that is, a family of multiplications, units and inversions on the sets $\mathrm{SchemeHomOver}\, t\, f$ of morphisms $\varphi \colon T \to A$ with $\varphi$ followed by $f$ equal to $t$, for all $R_0$-schemes $t \colon T \to \operatorname{Spec} R_0$, satisfying associativity, both unit laws, left inverses, and naturality of the multiplication under base change $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $\ell$ be a natural number, let $R'$ and $S'$ be commutative rings with $R'$ local, and let $\varphi \colon R' \to S'$ be a surjective ring homomorphism whose kernel satisfies $(\ker \varphi)^2 = 0$; assume moreover that the image of $\ell$ in $R'$ vanishes. Let $t \colon \operatorname{Spec} R' \to \operatorname{Spec} R_0$ be a structure morphism and let $x$ be a section over $t$, i.e. a morphism $\operatorname{Spec} R' \to A$ over $t$, whose base change along $\operatorname{Spec} \varphi$ (composition with $\operatorname{Spec} \varphi$, a section over $\operatorname{Spec} \varphi$ followed by $t$) is the unit section of $G$. Then the $\ell$-fold power of $x$, formed by iterating right multiplication by $x$ starting from the unit, equals the unit section $G.\mathrm{one}\, t$.
--
--   This is the standard statement that the kernel of the reduction map along a square-zero surjection is, for a relative group law, a module over the base ring, so that any integer vanishing in the base annihilates it; here it appears in the form "$\ell = 0$ in $R'$ kills square-zero deformations of the unit". It is used in the analysis of the $\ell$-torsion of Jacobians with good reduction, feeding the computation of the cotangent space of the kernel of the counit and the comparison of torsion points with dual-number sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_sqZero_of_natCast_eq_zero
    {R₀ : Type u} [CommRing R₀]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R₀)} (G : RelativeGroupLaw R₀ f)
    (ℓ : ℕ) (R' S' : CommRingCat.{u}) [IsLocalRing R'] (φ : R' ⟶ S') (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥) (hℓ : (ℓ : R') = 0)
    (t : Spec R' ⟶ Spec (CommRingCat.of R₀)) (x : SchemeHomOver t f)
    (hx : GoodReductionJacobian.schemeHomOverComp (Spec.map φ) rfl x = G.one (Spec.map φ ≫ t)) :
    G.nsmul t ℓ x = G.one t := by sorry
