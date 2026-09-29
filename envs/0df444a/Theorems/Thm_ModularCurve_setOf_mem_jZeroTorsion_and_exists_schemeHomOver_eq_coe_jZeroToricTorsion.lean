-- Prove2me | Theorems.Thm_ModularCurve_setOf_mem_jZeroTorsion_and_exists_schemeHomOver_eq_coe_jZeroToricTorsion
-- name    : ModularCurve.setOf_mem_jZeroTorsion_and_exists_schemeHomOver_eq_coe_jZeroToricTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/9d5d85bd-83e8-51cc-8e03-5f17b74d49d1
-- title:
--   Prime-to-p torsion extending over A equals toric torsion
-- statement:
--   Let $p$ be a prime, let $g \colon G \to \operatorname{Spec}\mathbb{Z}$ be a separated morphism of schemes, locally of finite type, and let $L$ be a relative group law for $g$ over $\mathbb{Z}$, i.e. a functorial group structure on the sets $\{\varphi \colon T \to G \mid \varphi \text{ over } \operatorname{Spec}\mathbb{Z}\}$, assumed commutative; for every $n \ge 1$ the induced endomorphism $L.\mathrm{schemeNsmul}\ n \colon G \to G$ (the $n$-fold sum of the identity $G$-point of $G$) is assumed flat, surjective and locally of finite presentation. Let $\mathrm{pts}$ be a bijection from $\mathrm{JZero}\ p$, the degree-zero divisor class group of the level-$p$ modular function field over $\overline{\mathbb{Q}}$, onto the $\overline{\mathbb{Q}}$-points of $g$, which is additive for $L.\mathrm{mul}$ and Galois-equivariant in the sense that the morphism underlying $\mathrm{pts}(\sigma \cdot x)$ is $\operatorname{Spec}(\sigma)$ followed by that of $\mathrm{pts}(x)$ for every $\sigma \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. Let $A \subseteq \overline{\mathbb{Q}}$ be a valuation subring in which $p$ is a non-unit, and put $n = (p-1)/\gcd(p-1,12)$. Assume that for every $y$ fixed by the inertia subgroup of $A$ over $\mathbb{Q}$ (in its image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$) the point $\mathrm{pts}(n y)$ factors through an $A$-point of $g$. Then for $m$ with $p \nmid m$, the set of $x$ with $m x = 0$ such that $\mathrm{pts}(x)$ factors through an $A$-point of $g$ coincides, as a subset, with $\mathrm{jZeroToricTorsion}\ p\ A\ m$, the intersection of the $m$-torsion with the image of the inertia-invariants under multiplication by $n$.
--
--   This is the torsion-level statement pinning which prime-to-$p$ torsion points of $J_0(p)$ over $\overline{\mathbb{Q}}$ extend over a place above $p$: exactly the toric ones, $J_0(p)[m] \cap n\, J_0(p)(\overline{\mathbb{Q}})^{I_A}$, where $n$ is the numerator of $(p-1)/12$. It is phrased over raw data (a scheme with a relative group law together with an additive Galois-equivariant identification of its $\overline{\mathbb{Q}}$-points with $J_0(p)$) so as to supply the corresponding field of the Néron identity-component data used by [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_setOf_mem_jZeroTorsion_and_exists_schemeHomOver_eq_coe_jZeroToricTorsion.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.setOf_mem_jZeroTorsion_and_exists_schemeHomOver_eq_coe_jZeroToricTorsion
    (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g]
    (L : RelativeGroupLaw ℤ g) (hcomm : L.IsCommutative)
    (hflat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n))
    (hsurj : ∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n))
    (hlfp : ∀ n : ℕ, 0 < n → LocallyOfFinitePresentation (L.schemeNsmul n))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g)
    (pts_add : ∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y))
    (pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hExt : ∀ y ∈ inertiaInvariantPoints p A,
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g,
        (pts (eisensteinNumerator p • y)).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1)
    (m : ℕ) (hm : ¬ p ∣ m) :
    {x : JZero p | x ∈ jZeroTorsion p m ∧
        ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g,
          (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1}
      = (jZeroToricTorsion p A m : Set (JZero p)) := by sorry
