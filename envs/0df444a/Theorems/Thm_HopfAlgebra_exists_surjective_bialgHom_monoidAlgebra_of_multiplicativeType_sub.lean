-- Prove2me | Theorems.Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub
-- name    : HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/dfbac106-0d50-5fca-b0f7-947ca1b4cced
-- title:
--   Multiplicative-type point subgroup yields a group-algebra quotient
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let $O$ be a subring of $\overline{\mathbb{Q}}$ contained in $A$ which is a discrete valuation ring in which $q$ is irreducible; write $I$ for the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ (the inertia subgroup of the decomposition subgroup, pushed forward along the inclusion of the latter). Assume an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ lies in $I$ exactly when it fixes $O$ pointwise, and that every element of $A$ fixed by all of $I$ lies in $O$. Let $H$ be a commutative ring which is a cocommutative Hopf algebra over $O$, finite and flat as an $O$-module. Let $J$ be an additive commutative group carrying a distributive action of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, and let $S \le M$ be additive subgroups of $J$. Suppose given a bijection $\mathrm{pts}$ from the $O$-algebra maps $H \to \overline{\mathbb{Q}}$, taken with their convolution monoid structure (`WithConv`), onto $M$, carrying convolution products to sums, and such that for $\sigma \in I$ and points $f, g$ with $g(x) = \sigma(f(x))$ for all $x \in H$ one has $\mathrm{pts}\,g = \sigma \cdot \mathrm{pts}\,f$ in $J$. Suppose finally that $S$ has cardinality $q^{a}$ for some $a \in \mathbb{N}$, and that whenever $\sigma \in I$ and $c \in \mathbb{N}$ satisfy $\sigma \zeta = \zeta^{c}$ for all $q$-th roots of unity $\zeta$ in $\overline{\mathbb{Q}}$, then $\sigma$ acts on $S$ as multiplication by $c$. The conclusion is that there exists a surjective $O$-bialgebra homomorphism $p$ from $H$ to the group algebra $O[(\mathbb{Z}/q)^{a}]$, i.e. `MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q))`, such that an $O$-algebra map $f : H \to \overline{\mathbb{Q}}$ factors as $p$ followed by some $O$-algebra map $g$ out of the group algebra if and only if the element of $J$ attached to $f$ by $\mathrm{pts}$ lies in $S$.
--
--   This is the form in which Raynaud's analysis of finite flat group schemes of multiplicative type over an unramified base enters the argument: a subgroup of points cut out by its order $q^{a}$ and its inertia type is realised as the points factoring through a group-algebra quotient of $H$. It is used in the proof of [`HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual`](thm.html#HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOirr : Irreducible ((q : ℕ) : ↥O))
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (H : Type) [CommRing H] [HopfAlgebra ↥O H]
    [Module.Finite ↥O H] [Module.Flat ↥O H] [Coalgebra.IsCocomm ↥O H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M S : AddSubgroup J) (hSM : S ≤ M)
    (pts : WithConv (H →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M)
    (hadd : ∀ f g, pts (f * g) = pts f + pts g)
    (hact : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (H →ₐ[↥O] AlgebraicClosure ℚ),
      (∀ x : H, g x = σ (f x)) → ((pts g : ↥M) : J) = σ • ((pts f : ↥M) : J))
    (a : ℕ) (hcardS : Nat.card ↥S = q ^ a)
    (hS : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) → ∀ x ∈ S, σ • x = c • x) :
    ∃ p : H →ₐc[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)),
      Function.Surjective p ∧
      ∀ f : H →ₐ[↥O] AlgebraicClosure ℚ,
        (∃ g : MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)) →ₐ[↥O] AlgebraicClosure ℚ,
            g.comp (p : H →ₐ[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q))) = f) ↔
          ((pts (WithConv.toConv f) : ↥M) : J) ∈ S := by sorry
