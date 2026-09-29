-- Prove2me | Theorems.Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid
-- name    : HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/b9234c43-f85a-5b97-832c-b1718640f7c4
-- title:
--   Inertia-cyclotomic point submonoids are cut out by O[(ℤ/q)ᵃ]
-- statement:
--   Let $q$ be an odd prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and write $I = A.\mathrm{inertiaSubgroupIn}\ \mathbb{Q}$ for the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained as the image of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup. Let $O$ be a commutative domain equipped with an algebra map $O \to \overline{\mathbb{Q}}$ whose associated action is faithful, with image contained in $A$, such that $O$ is a discrete valuation ring and $q$ is irreducible in $O$; assume moreover that an automorphism $\sigma$ lies in $I$ precisely when it fixes the image of $O$ pointwise, and that every element of $A$ fixed by all of $I$ lies in the image of $O$. Let $HO$ be a commutative ring that is a Hopf algebra over $O$, module-finite and flat over $O$, with cocommutative comultiplication. Let $D$ be a submonoid of the $O$-algebra maps $HO \to \overline{\mathbb{Q}}$ under the convolution product, with $\#D = q^{a}$, subject to: for every $\sigma \in I$ and every $c \in \mathbb{N}$ with $\sigma\zeta = \zeta^{c}$ for all $\zeta$ with $\zeta^{q} = 1$, and every $f \in D$ and every $O$-algebra map $g$ with $g(h) = \sigma(f(h))$ for all $h \in HO$, one has $g = f^{c}$ in the convolution monoid. The conclusion is that there exists a surjective $O$-bialgebra map $p_{0} \colon HO \to O[(\mathbb{Z}/q\mathbb{Z})^{a}]$ (the monoid algebra on the multiplicative monoid $\mathrm{Fin}\ a \to \mathbb{Z}/q$) such that an $O$-algebra map $f \colon HO \to \overline{\mathbb{Q}}$ factors as $g \circ p_{0}$ for some $O$-algebra map $g$ on $O[(\mathbb{Z}/q\mathbb{Z})^{a}]$ if and only if $f$, viewed in the convolution monoid, lies in $D$.
--
--   This is an abstract-base form of Raynaud's analysis of finite flat group schemes killed by $q$: the closed subscheme of $\operatorname{Spec} HO$ cut out by $p_{0}$ is $\mu_{q}^{a}$, and its $\overline{\mathbb{Q}}$-points are exactly the prescribed submonoid $D$ on which inertia acts through the mod $q$ cyclotomic character. It is used in the Hopf-algebra analysis of the Néron models and of the $q$-division points attached to the Frey curve, being cited by [`HopfAlgebra.eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant`](thm.html#HopfAlgebra.eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant), [`KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial`](thm.html#KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial) and [`ModularCurve.JHNeronObjectAtP.reducesToOne_of_inertia_cyclotomic_of_mem_finPts`](thm.html#ModularCurve.JHNeronObjectAtP.reducesToOne_of_inertia_cyclotomic_of_mem_finPts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)] [FaithfulSMul O (AlgebraicClosure ℚ)]
    (hOA : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : O, algebraMap O (AlgebraicClosure ℚ) x = y)
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO]
    (D : Submonoid (WithConv (HO →ₐ[O] AlgebraicClosure ℚ)))
    (a : ℕ) (hcardD : Nat.card ↥D = q ^ a)
    (hD : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f ∈ D, ∀ g : WithConv (HO →ₐ[O] AlgebraicClosure ℚ), (∀ h : HO, g h = σ (f h)) → g = f ^ c) :
    ∃ p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q)),
      Function.Surjective p₀ ∧
      ∀ f : HO →ₐ[O] AlgebraicClosure ℚ,
        (∃ g : MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] AlgebraicClosure ℚ,
            g.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) = f) ↔
          WithConv.toConv f ∈ D := by sorry
