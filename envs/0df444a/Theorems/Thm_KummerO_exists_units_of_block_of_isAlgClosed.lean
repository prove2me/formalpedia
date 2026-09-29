-- Prove2me | Theorems.Thm_KummerO_exists_units_of_block_of_isAlgClosed
-- name    : KummerO.exists_units_of_block_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/dc74001b-1ca2-56ac-80d3-07734423fb22
-- title:
--   Kummer units for a block of q-torsion Hopf algebra points
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $K \subseteq L$ be fields with $L$ algebraically closed of characteristic $0$ and $L$ a $K$-algebra, and let $A \subseteq L$ be a valuation subring with $(q : L)$ a non-unit of $A$; write $I =$ `A.inertiaSubgroupIn K` for the image in $L \simeq_{\mathrm{alg}[K]} L$ of the inertia subgroup of $A$ over $K$ under the inclusion of the decomposition subgroup. Let $O$ be a discrete valuation ring that is a domain in which $q$ is irreducible, given as an $O$-algebra structure on $A$ together with an injective ring homomorphism $\iota : O \to A$ agreeing with the structure map, such that an automorphism $\sigma$ lies in $I$ precisely when it fixes $\iota(x)$ for all $x \in O$, and every $a \in A$ fixed by all of $I$ lies in the range of $\iota$. Let $B$ be a commutative, cocommutative Hopf $O$-algebra, finite and free as an $O$-module, such that for every commutative $O$-algebra $T$ every element of the convolution group `WithConv (B →ₐ[O] T)` satisfies $f^q = 1$. Let $\Lambda$ be a finite abelian group with $q \cdot g = 0$ for all $g$, and let $p_0 : B \to O[\Lambda]$ be a surjective bialgebra homomorphism onto the monoid algebra of $\Lambda$ written multiplicatively. Let $e \in B$ be an idempotent with counit $0$ such that the set of $\psi$ in the convolution group of $O$-algebra maps $B \to A$ with $\psi(e) = 1$ is non-empty of cardinality $\#\Lambda$. Then there are families $U, \beta : \Lambda \to L$ such that: the valuation of $U_g$ attached to $A$ equals $1$ for every $g$, so that $U_g$ is a unit of $A$; each $U_g$ is fixed by every $\sigma \in I$; $\beta_g^{\,q} = U_g$; and every $\sigma \in I$ which fixes all $q$-th roots of unity $\zeta \in L$ and all the $\beta_g$ satisfies $\sigma(\psi(b)) = \psi(b)$ for every $\psi$ in the convolution group of $O$-algebra maps $B \to A$ with $\psi(e) = 1$ and every $b \in B$.
--
--   This is the Kummer-theoretic step for a single block of points of a finite flat $q$-torsion Hopf algebra: the block is cut out by the idempotent $e$, and its points are controlled by $q$-th roots of finitely many inertia-fixed units of $A$, in the style of Raynaud's analysis of group schemes of type $(q,\dots,q)$ and of $\mu_q$-torsors. It is used by [`KummerO.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed`](thm.html#KummerO.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed) to conclude that suitable inertia acts trivially on such points, and it relies on the torsor grading of the block together with the existence of generators whose $q$-th powers are units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KummerO_exists_units_of_block_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem KummerO.exists_units_of_block_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : (L ≃ₐ[K] L), σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ ((ι x : ↥A) : L) = ((ι x : ↥A) : L))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn K, σ (a : L) = (a : L)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (hΛq : ∀ g : Λ, q • g = 0)
    (p₀ : B →ₐc[O] MonoidAlgebra O (Multiplicative Λ)) (hsurj : Function.Surjective p₀)
    (e : B) (hidem : IsIdempotentElem e) (hcounit : Coalgebra.counit (R := O) e = 0)
    (hcard : Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ψ e = 1} = Fintype.card Λ)
    (hne : ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1) :
    ∃ (U β : Λ → L),
      (∀ g, A.valuation (U g) = 1) ∧
      (∀ g, ∀ σ ∈ A.inertiaSubgroupIn K, σ (U g) = U g) ∧
      (∀ g, (β g) ^ q = U g) ∧
      (∀ σ ∈ A.inertiaSubgroupIn K, (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ) → (∀ g, σ (β g) = β g) →
        ∀ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1 → ∀ b : B, σ ((WithConv.ofConv ψ b : ↥A) : L) = ((WithConv.ofConv ψ b : ↥A) : L)) := by sorry
