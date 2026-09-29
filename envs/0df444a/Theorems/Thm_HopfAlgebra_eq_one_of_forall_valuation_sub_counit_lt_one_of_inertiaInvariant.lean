-- Prove2me | Theorems.Thm_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant
-- name    : HopfAlgebra.eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/d08e976b-7d1d-56dd-b530-f927f7b7807a
-- title:
--   Inertia-invariant characters kill points reducing to the identity
-- statement:
--   Fix a prime $q$ with $q \neq 2$ and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`; write $I_A$ for `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup. Let $O$ be a commutative domain with an algebra structure over $\overline{\mathbb{Q}}$ whose action is faithful, such that: every element of $O$ maps into $A$; $O$ is a discrete valuation ring in which the image of $q$ is irreducible; an element $\sigma$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lies in $I_A$ exactly when it fixes the image of $O$ pointwise; and every $y \in A$ fixed by all of $I_A$ lies in the image of $O$. Let $HO$ be a commutative ring carrying a Hopf $O$-algebra structure which is module-finite and flat over $O$ and cocommutative, and let $\mathrm{Pt} =$ `WithConv (HO →ₐ[O] AlgebraicClosure ℚ)` be the monoid of $O$-algebra maps $HO \to \overline{\mathbb{Q}}$ under convolution. Assume every $f \in \mathrm{Pt}$ satisfies $f^q = 1$. Let $\varphi \colon \mathrm{Pt} \to \overline{\mathbb{Q}}$ be a monoid homomorphism which is inertia-invariant in the sense that $\varphi(g) = \varphi(f)$ whenever $\sigma \in I_A$ and $g(h) = \sigma(f(h))$ for all $h \in HO$. Then any $f \in \mathrm{Pt}$ with $A$-valuation of $f(h) - \varepsilon(h)$ strictly less than $1$ for every $h \in HO$, where $\varepsilon$ is the counit of $HO$ composed with $O \to \overline{\mathbb{Q}}$, satisfies $\varphi(f) = 1$.
--
--   This is the statement that an inertia-invariant character of the $\overline{\mathbb{Q}}$-points of a finite flat commutative cocommutative $q$-torsion group scheme over the inertia ring is trivial on the points reducing to the identity, for odd $q$; it rests on Cartier duality together with Raynaud's description of such group schemes at absolute ramification index one. It is used in the analysis of the Weil pairing on toric points of the Néron model of a modular curve at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant
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
    (hHOq : ∀ f : WithConv (HO →ₐ[O] AlgebraicClosure ℚ), f ^ q = 1)
    (φ : WithConv (HO →ₐ[O] AlgebraicClosure ℚ) →* AlgebraicClosure ℚ)
    (hφ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (HO →ₐ[O] AlgebraicClosure ℚ),
      (∀ h : HO, g h = σ (f h)) → φ g = φ f)
    (f : WithConv (HO →ₐ[O] AlgebraicClosure ℚ))
    (hf : ∀ h : HO, A.valuation (f h - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) :
    φ f = 1 := by sorry
