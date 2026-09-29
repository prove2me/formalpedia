-- Prove2me | Theorems.Thm_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
-- name    : KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/2e56e148-fb0c-51eb-b873-48efc3edde40
-- title:
--   Block idempotents indexed by cosets of a cyclotomic submonoid of points
-- statement:
--   Let $q$ be an odd prime, let $L/K$ be an extension with $L$ algebraically closed of characteristic $0$, and let $A\subseteq L$ be a valuation subring with $q$ a non-unit of $A$; write $I\le L\simeq_K L$ for the image in $\operatorname{Aut}(L/K)$ of the inertia subgroup of the decomposition subgroup of $A$. Let $O$ be a discrete valuation domain in which $q$ is irreducible, equipped with an $O$-algebra structure on $A$ and an injective ring map $\iota\colon O\to A$ agreeing with the structure map, such that $\sigma\in I$ precisely when $\sigma$ fixes every $\iota(x)$ pointwise, and every element of $A$ fixed by all of $I$ lies in the range of $\iota$. Let $B$ be a commutative, cocommutative Hopf $O$-algebra, finite and free as an $O$-module, such that for every commutative $O$-algebra $T$ each element of the convolution monoid $\mathrm{WithConv}\,(B\to_{\mathrm{alg}[O]}T)$ satisfies $f^q=1$. Let $n\colon\operatorname{Aut}(L/K)\to\mathbb N$ satisfy $\sigma\zeta=\zeta^{n(\sigma)}$ for all $\zeta\in L$ with $\zeta^q=1$. Let $D$ be a submonoid of the convolution monoid of $A$-points of $B$ such that: for $\sigma\in I$ and $f\in D$, any point $g$ with $g(b)=\sigma(f(b))$ in $L$ for all $b\in B$ equals $f^{n(\sigma)}$; and for $\sigma\in I$ and arbitrary points $f,g$ with $g(b)=\sigma(f(b))$ for all $b$, one has $g=fd$ for some $d\in D$. Let $\Lambda$ be a finite abelian group with $\#\Lambda=\#D$. Then there exist $N$ and $\varepsilon_0,\dots,\varepsilon_N\in B$ such that each $\varepsilon_i$ is idempotent, $\varepsilon_i\varepsilon_j=0$ for $i\ne j$, $\sum_i\varepsilon_i=1$, the counit sends $\varepsilon_0$ to $1$ and every other $\varepsilon_i$ to $0$; each $A$-point $\psi$ satisfies $\psi(\varepsilon_i)=1$ for exactly one $i$; $\psi\in D$ if and only if $\psi(\varepsilon_0)=1$; each index $i$ is attained by some point; whenever $\psi(\varepsilon_i)=1$, a point $\varphi$ satisfies $\varphi(\varepsilon_i)=1$ if and only if $\varphi=\psi d$ with $d\in D$; each block $\{\psi:\psi(\varepsilon_i)=1\}$ has exactly $\#\Lambda$ elements; and $(N+1)\cdot\#D$ equals the number of $A$-points of $B$.
--
--   This is the combinatorial decomposition step in the Raynaud-style analysis of a finite flat cocommutative $q$-torsion group scheme over the inertia-fixed discrete valuation ring: the $A$-points split into $N+1$ cosets of the cyclotomic submonoid $D$, and the splitting is realised by an orthogonal family of idempotents in $B$ itself, with $\varepsilon_0$ cutting out $D$ and normalised by the counit. It is used by [`KummerO.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed`](thm.html#KummerO.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : (L ≃ₐ[K] L), σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ ((ι x : ↥A) : L) = ((ι x : ↥A) : L))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn K, σ (a : L) = (a : L)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (n : (L ≃ₐ[K] L) → ℕ)
    (hn : ∀ σ (ζ : L), ζ ^ q = 1 → σ ζ = ζ ^ n σ)
    (D : Submonoid (WithConv (B →ₐ[O] ↥A)))
    (hDcyc : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ f ∈ D, ∀ g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : L) = σ ((WithConv.ofConv f b : ↥A) : L)) → g = f ^ n σ)
    (hquot : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ f g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : L) = σ ((WithConv.ofConv f b : ↥A) : L)) → ∃ d ∈ D, g = f * d)
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
