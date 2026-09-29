-- Prove2me | Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints
-- name    : HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/4b69e92b-1017-542a-8ee8-184312125cb6
-- title:
--   Galois-stable chains of L-points and flat Hopf quotient flags
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a $K$-algebra, and let $R$ be a principal ideal domain that is an $L$-algebra with $\operatorname{algebraMap} R \to L$ injective, subject to the fixed-point hypothesis: every $c \in L$ fixed by all $K$-algebra automorphisms $\sigma$ of $L$ which fix $\operatorname{algebraMap} R \to L$ pointwise satisfies $c\,b = a$ for some $a,b \in R$ with $b \neq 0$ in $L$. Let $H$ be a commutative Hopf $R$-algebra that is of finite type and flat over $R$, let $M$ be a finite abelian group, and let $e$ be a bijection from `WithConv (H →ₐ[R] L)`, the $R$-algebra maps $H \to L$ with the convolution product, onto $M$ with $e(fg) = e(f) + e(g)$. Let $act$ be a function assigning to each $\sigma \in \operatorname{Aut}_K(L)$ a self-map of $M$ such that whenever $g(h) = \sigma(f(h))$ for all $h \in H$ one has $e(g) = act\,\sigma\,(e f)$. Finally let $N_0 \le N_1 \le \dots \le N_n = \top$ be subgroups of $M$ indexed by `Fin (n+1)`, each stable under every $act\,\sigma$. The conclusion produces types $B_i$ ($i \in$ `Fin (n+1)`) with commutative ring and Hopf $R$-algebra structures, bialgebra maps $\pi_i : H \to B_i$ and $\varphi_i : B_{i+1} \to B_i$, such that each $B_i$ is of finite type and flat over $R$, all $\pi_i$ and $\varphi_i$ are surjective, $\pi_{i+1}$ followed by $\varphi_i$ equals $\pi_i$, $\pi_n$ is bijective, and for every $i$ and every $R$-algebra map $f : H \to L$, $f$ factors as $\pi_i$ followed by some $R$-algebra map $B_i \to L$ if and only if $e(f) \in N_i$; moreover if $H$ is cocommutative then so is each $B_i$, and if $H$ is finite as an $R$-module then each $B_i$ is finite as an $R$-module, with $\operatorname{finrank}_R B_i = \#N_i$ for all $i \neq n$ (the top index being excluded from the rank assertion).
--
--   This is the Hopf-algebra form of taking the schematic closure in $\operatorname{Spec} H$ of a chain of Galois-stable finite subgroups of the $L$-points, yielding a flag of flat finite-type Hopf quotients whose $L$-points are exactly the prescribed subgroups. Stated over an arbitrary extension $K \subseteq L$ and an arbitrary principal ideal domain $R \subseteq L$ satisfying the fixed-point condition, it is the form used by the specialisations to $R = \mathbb{Z}_p$ that extract finite flat group schemes with prescribed point groups and inertia behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R L]
    (hR : Function.Injective (algebraMap R L))
    (hfix : ∀ c : L, (∀ σ : L ≃ₐ[K] L, (∀ r : R, σ (algebraMap R L r) = algebraMap R L r) → σ c = c) →
      ∃ a b : R, algebraMap R L b ≠ 0 ∧ c * algebraMap R L b = algebraMap R L a)
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    (M : Type) [AddCommGroup M] [Finite M]
    (e : WithConv (H →ₐ[R] L) ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g)
    (act : (L ≃ₐ[K] L) → M → M)
    (hact : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H →ₐ[R] L)),
        (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (n : ℕ) (N : Fin (n + 1) → AddSubgroup M)
    (hmono : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (htop : N (Fin.last n) = ⊤)
    (hstab : ∀ (i : Fin (n + 1)) (σ : L ≃ₐ[K] L) (x : M), x ∈ N i → act σ x ∈ N i) :
    ∃ (B : Fin (n + 1) → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, HopfAlgebra R (B i))
      (π : ∀ i, H →ₐc[R] B i) (φ : ∀ i : Fin n, B i.succ →ₐc[R] B i.castSucc),
      (∀ i, Algebra.FiniteType R (B i)) ∧ (∀ i, Module.Flat R (B i)) ∧
      (∀ i, Function.Surjective (π i)) ∧ (∀ i, Function.Surjective (φ i)) ∧
      (∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc) ∧
      Function.Bijective (π (Fin.last n)) ∧
      (∀ (i : Fin (n + 1)) (f : H →ₐ[R] L),
        (∃ g : B i →ₐ[R] L, g.comp (π i : H →ₐ[R] B i) = f) ↔
          e (WithConv.toConv f) ∈ N i) ∧
      (Coalgebra.IsCocomm R H → ∀ i, Coalgebra.IsCocomm R (B i)) ∧
      (Module.Finite R H → ∀ i, Module.Finite R (B i) ∧
        (i ≠ Fin.last n → Module.finrank R (B i) = Nat.card (N i))) := by sorry
