-- Prove2me | Theorems.Thm_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial
-- name    : KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/5763ba92-9cbb-5d97-ad91-442883cce2be
-- title:
--   Block idempotents for points with inertia-trivial quotient
-- statement:
--   Fix an odd prime $q$ and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$, in the sense that $q$ belongs to the non-units of $A$; write $I =$ `A.inertiaSubgroupIn ℚ` for the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ under the inclusion of its decomposition subgroup. Let $O$ be a discrete valuation domain in which $q$ is irreducible, equipped with an $O$-algebra structure on $A$ and an injective ring homomorphism $\iota : O \to A$ that agrees with the structure map, such that an automorphism $\sigma$ lies in $I$ precisely when it fixes $\iota(x)$ for all $x \in O$, and such that every element of $A$ fixed by all of $I$ lies in the image of $\iota$. Let $B$ be a commutative, cocommutative Hopf algebra over $O$ that is finite and free as an $O$-module, and assume that for every commutative $O$-algebra $T$ each element of the convolution monoid `WithConv (B →ₐ[O] T)` satisfies $f^q = 1$. Let $n : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathbb{N}$ satisfy $\sigma\zeta = \zeta^{n(\sigma)}$ for every $q$-th root of unity $\zeta$. Let $D$ be a submonoid of the convolution monoid $P =$ `WithConv (B →ₐ[O] A)` of $A$-valued points, subject to two conditions: for $\sigma \in I$, $f \in D$ and $g \in P$, if $g(b) = \sigma(f(b))$ for all $b \in B$ then $g = f^{n(\sigma)}$; and for $\sigma \in I$ and arbitrary $f, g \in P$, if $g(b) = \sigma(f(b))$ for all $b \in B$ then $g = fd$ for some $d \in D$. Finally let $\Lambda$ be a finite abelian group with $\#\Lambda = \#D$ (it enters only through this cardinality). The conclusion asserts the existence of $N \in \mathbb{N}$ and elements $\varepsilon_0,\dots,\varepsilon_N \in B$ that are idempotent, pairwise orthogonal, sum to $1$, with counit $1$ at $\varepsilon_0$ and $0$ at $\varepsilon_i$ for $i \neq 0$, and such that: each $\psi \in P$ satisfies $\psi(\varepsilon_i) = 1$ for exactly one index $i$; $\psi \in D$ if and only if $\psi(\varepsilon_0) = 1$; each index $i$ is attained by some $\psi$; whenever $\psi(\varepsilon_i) = 1$, the points $\varphi$ with $\varphi(\varepsilon_i) = 1$ are exactly those of the form $\psi d$ with $d \in D$; each such block has exactly $\#\Lambda$ elements; and $(N+1)\cdot\#D = \#P$.
--
--   The idempotents cut $\operatorname{Spec} B$ into the fibres of its quotient by the part of the Cartier dual on which inertia acts through the cyclotomic character, the quotient being constant over the strictly henselian base; the block containing the unit section corresponds to $D$. It is the blocks-existence step used by [`WRay.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial`](thm.html#WRay.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial), and is stated without any hypothesis on the rank of $B$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : Γℚ, σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ ((ι x : ↥A) : AlgebraicClosure ℚ) = ((ι x : ↥A) : AlgebraicClosure ℚ))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (n : Γℚ → ℕ)
    (hn : ∀ σ (ζ : AlgebraicClosure ℚ), ζ ^ q = 1 → σ ζ = ζ ^ n σ)
    (D : Submonoid (WithConv (B →ₐ[O] ↥A)))
    (hDcyc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f ∈ D, ∀ g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv f b : ↥A) : AlgebraicClosure ℚ)) → g = f ^ n σ)
    (hquot : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv f b : ↥A) : AlgebraicClosure ℚ)) → ∃ d ∈ D, g = f * d)
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (hΛ : Nat.card Λ = Nat.card ↥D) :
    ∃ (N : ℕ) (ε : Fin (N + 1) → B),
      (∀ i, IsIdempotentElem (ε i)) ∧
      (∀ i j, i ≠ j → ε i * ε j = 0) ∧
      (∑ i, ε i) = 1 ∧
      Coalgebra.counit (R := O) (ε 0) = 1 ∧
      (∀ i, i ≠ 0 → Coalgebra.counit (R := O) (ε i) = 0) ∧
      (∀ ψ : WithConv (B →ₐ[O] ↥A), ∃! i : Fin (N + 1), ψ (ε i) = 1) ∧
      (∀ ψ : WithConv (B →ₐ[O] ↥A), ψ ∈ D ↔ ψ (ε 0) = 1) ∧
      (∀ i : Fin (N + 1), ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ (ε i) = 1) ∧
      (∀ (i : Fin (N + 1)) (ψ φ : WithConv (B →ₐ[O] ↥A)), ψ (ε i) = 1 → (φ (ε i) = 1 ↔ ∃ d ∈ D, φ = ψ * d)) ∧
      (∀ i : Fin (N + 1), Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ψ (ε i) = 1} = Fintype.card Λ) ∧
      (N + 1) * Nat.card ↥D = Nat.card (WithConv (B →ₐ[O] ↥A)) := by sorry
