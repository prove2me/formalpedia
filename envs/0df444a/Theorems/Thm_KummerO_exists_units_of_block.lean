-- Prove2me | Theorems.Thm_KummerO_exists_units_of_block
-- name    : KummerO.exists_units_of_block
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/89f2ef68-2599-506b-b18a-381a5cb66c3a
-- title:
--   Kummer generators for one block of a finite free Hopf algebra
-- statement:
--   Let $q$ be an odd prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $q$ a non-unit of $A$, and write $I =$ `A.inertiaSubgroupIn ℚ` for the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ inside its decomposition subgroup. Let $O$ be a discrete valuation domain in which $q$ is irreducible, equipped with an $O$-algebra structure on $A$ and an injective ring homomorphism $\iota : O \to A$ agreeing with the structure map, such that $\sigma \in I$ holds exactly when $\sigma$ fixes every $\iota(x)$, and every $a \in A$ fixed by all of $I$ lies in the range of $\iota$. Let $B$ be a commutative, cocommutative Hopf $O$-algebra, finite and free as an $O$-module, whose group of $T$-points under convolution is killed by $q$ for every commutative $O$-algebra $T$. Let $\Lambda$ be a finite abelian group killed by $q$, let $p_0 : B \to O[\Lambda]$ be a surjective bialgebra homomorphism onto the group algebra of $\Lambda$, and let $e \in B$ be an idempotent with counit $0$ such that the set of convolution points $\psi : B \to A$ with $\psi(e) = 1$ is non-empty of cardinality $\#\Lambda$. Then there are families $U, \beta : \Lambda \to \overline{\mathbb{Q}}$ such that each $U_g$ has $A$-valuation $1$ (that is, is a unit of $A$) and is fixed by $I$, each $\beta_g$ satisfies $\beta_g^{\,q} = U_g$, and every $\sigma \in I$ which fixes all $q$-th roots of unity and all the $\beta_g$ fixes $\psi(b)$ for every $O$-algebra homomorphism $\psi : B \to A$ with $\psi(e) = 1$ and every $b \in B$.
--
--   This is the Kummer-theoretic step in the analysis of finite flat group schemes killed by $q$ over the inertia-fixed discrete valuation ring, in the style of Raynaud and Mazur: the block $Be$ cut out by the idempotent $e$ carries a rank-one $\Lambda$-graded torsor structure, the $q$-th power of a generator of each graded line is a unit, and a point of the block is determined by $q$-th roots of those units. It feeds the unit-Kummer core [`WRay.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial`](thm.html#WRay.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial), and is proved from [`HopfAlgebra.blockPieces_torsor_core`](thm.html#HopfAlgebra.blockPieces_torsor_core) together with [`HopfAlgebra.exists_unit_pow_of_torsor_grading_nsmul`](thm.html#HopfAlgebra.exists_unit_pow_of_torsor_grading_nsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KummerO_exists_units_of_block.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem KummerO.exists_units_of_block
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : Γℚ, σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ ((ι x : ↥A) : AlgebraicClosure ℚ) = ((ι x : ↥A) : AlgebraicClosure ℚ))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (hΛq : ∀ g : Λ, q • g = 0)
    (p₀ : B →ₐc[O] MonoidAlgebra O (Multiplicative Λ)) (hsurj : Function.Surjective p₀)
    (e : B) (hidem : IsIdempotentElem e) (hcounit : Coalgebra.counit (R := O) e = 0)
    (hcard : Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ψ e = 1} = Fintype.card Λ)
    (hne : ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1) :
    ∃ (U β : Λ → AlgebraicClosure ℚ),
      (∀ g, A.valuation (U g) = 1) ∧
      (∀ g, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (U g) = U g) ∧
      (∀ g, (β g) ^ q = U g) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ) → (∀ g, σ (β g) = β g) →
        ∀ ψ : WithConv (B →ₐ[O] ↥A), ψ e = 1 → ∀ b : B, σ ((WithConv.ofConv ψ b : ↥A) : AlgebraicClosure ℚ) = ((WithConv.ofConv ψ b : ↥A) : AlgebraicClosure ℚ)) := by sorry
