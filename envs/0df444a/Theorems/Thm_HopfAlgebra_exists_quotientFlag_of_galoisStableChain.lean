-- Prove2me | Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain
-- name    : HopfAlgebra.exists_quotientFlag_of_galoisStableChain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/b3c6b3c7-83cd-5364-8630-0d3204b6473d
-- title:
--   Flat Hopf quotients cutting out a Galois-stable chain of points
-- statement:
--   Let $R$ be a commutative domain which is a principal ideal ring, equipped with an $R$-algebra structure on $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` whose structure map $R \to \overline{\mathbb Q}$ is injective, and let $H$ be a commutative ring carrying a Hopf $R$-algebra structure which is of finite type as an $R$-algebra and flat as an $R$-module. Let $M$ be a finite additive abelian group and $e$ a bijection from the set of $R$-algebra maps $H \to \overline{\mathbb Q}$, viewed through `WithConv` with its convolution multiplication, onto $M$, satisfying $e(f*g) = e(f)+e(g)$. Let $act$ assign to each $\sigma \in \operatorname{Aut}(\overline{\mathbb Q}/\mathbb Q)$ a map $M \to M$ such that whenever $g(h) = \sigma(f(h))$ for all $h \in H$ one has $e(g) = act\,\sigma\,(e(f))$. Let $n \in \mathbb N$ and let $N_0 \le N_1 \le \cdots \le N_n$ be subgroups of $M$ indexed by `Fin (n+1)`, increasing in the stated sense, with $N_n = \top$, each $N_i$ carried into itself by every $act\,\sigma$. Then there are types $B_i$ ($i \in$ `Fin (n+1)`) with commutative ring and Hopf $R$-algebra structures, bialgebra maps $\pi_i : H \to B_i$ and $\varphi_i : B_{i+1} \to B_i$, such that each $B_i$ is of finite type and flat over $R$; all $\pi_i$ and $\varphi_i$ are surjective; $\pi_{i+1}$ followed by $\varphi_i$ equals $\pi_i$; $\pi_n$ is bijective; for every $i$ and every $R$-algebra map $f : H \to \overline{\mathbb Q}$, $f$ factors as $\pi_i$ followed by some $R$-algebra map $B_i \to \overline{\mathbb Q}$ if and only if $e(f) \in N_i$; if the comultiplication of $H$ is cocommutative then so is that of each $B_i$; and if $H$ is a finite $R$-module then so is each $B_i$, with $\operatorname{finrank}_R B_i = \#N_i$ for every $i \ne n$ (the top index being excluded from the rank assertion).
--
--   This is the construction of the schematic closure in $\operatorname{Spec} H$ of a Galois-stable chain of finite subgroups of the group of $\overline{\mathbb Q}$-points, realised Hopf-algebraically as a flag of flat finite-type Hopf quotients of $H$ whose $\overline{\mathbb Q}$-points are exactly the prescribed subgroups. It is used in the construction of finite flat group schemes with prescribed point groups and Galois action, for instance in the results producing Hopf quotients with trivial inertia action and the surjections onto monoid-algebra models over cyclotomic bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_quotientFlag_of_galoisStableChain
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R (AlgebraicClosure ℚ)]
    (hR : Function.Injective (algebraMap R (AlgebraicClosure ℚ)))
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    (M : Type) [AddCommGroup M] [Finite M]
    (e : WithConv (H →ₐ[R] AlgebraicClosure ℚ) ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g)
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M → M)
    (hact : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[R] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (n : ℕ) (N : Fin (n + 1) → AddSubgroup M)
    (hmono : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (htop : N (Fin.last n) = ⊤)
    (hstab : ∀ (i : Fin (n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M),
        x ∈ N i → act σ x ∈ N i) :
    ∃ (B : Fin (n + 1) → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, HopfAlgebra R (B i))
      (π : ∀ i, H →ₐc[R] B i) (φ : ∀ i : Fin n, B i.succ →ₐc[R] B i.castSucc),
      (∀ i, Algebra.FiniteType R (B i)) ∧ (∀ i, Module.Flat R (B i)) ∧
      (∀ i, Function.Surjective (π i)) ∧ (∀ i, Function.Surjective (φ i)) ∧
      (∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc) ∧
      Function.Bijective (π (Fin.last n)) ∧
      (∀ (i : Fin (n + 1)) (f : H →ₐ[R] AlgebraicClosure ℚ),
        (∃ g : B i →ₐ[R] AlgebraicClosure ℚ, g.comp (π i : H →ₐ[R] B i) = f) ↔
          e (WithConv.toConv f) ∈ N i) ∧
      (Coalgebra.IsCocomm R H → ∀ i, Coalgebra.IsCocomm R (B i)) ∧
      (Module.Finite R H → ∀ i, Module.Finite R (B i) ∧
        (i ≠ Fin.last n → Module.finrank R (B i) = Nat.card (N i))) := by sorry
