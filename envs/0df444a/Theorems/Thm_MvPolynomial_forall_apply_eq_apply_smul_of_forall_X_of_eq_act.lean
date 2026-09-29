-- Prove2me | Theorems.Thm_MvPolynomial_forall_apply_eq_apply_smul_of_forall_X_of_eq_act
-- name    : MvPolynomial.forall_apply_eq_apply_smul_of_forall_X_of_eq_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/1b5dbf99-2073-51d8-a62a-5e822eb3131b
-- title:
--   From generators to all of ℤ[Xₙ]: additive intertwining
-- statement:
--   Let $\sigma$, $E$, $M$, $R$ be types, with $M$ an abelian group carrying a module structure over the polynomial ring $\mathrm{MvPolynomial}\ \sigma\ \mathbb{Z}$ and $R$ an abelian group. Let $K : E \to \mathrm{Prop}$ be a predicate on $E$, let $\mathrm{mul} : E \to E \to E$ be a binary operation, and let $\mathrm{act} : \mathrm{MvPolynomial}\ \sigma\ \mathbb{Z} \to E \to E$ be a map, subject to four hypotheses: $K$ is stable under every $\mathrm{act}\ t$; for $x$ with $K\,x$ one has $\mathrm{act}\,(st)\,x = \mathrm{act}\,t\,(\mathrm{act}\,s\,x)$, $\mathrm{act}\,(s+t)\,x = \mathrm{mul}\,(\mathrm{act}\,s\,x)\,(\mathrm{act}\,t\,x)$, and $\mathrm{act}\,1\,x = x$. Let $\tau$ assign to each element of the subtype $\{x : E \mathbin{/\!/} K\,x\}$ an additive monoid homomorphism $M \to R$, such that $\tau z = \tau x + \tau y$ whenever $z$, $x$, $y$ lie in that subtype and the underlying element of $z$ equals $\mathrm{mul}$ of those of $x$ and $y$; and assume that for each $n : \sigma$ and all $x, y$ in the subtype with $y = \mathrm{act}\,(X\ n)\,x$ one has $\tau y\,g = \tau x\,(X\ n \cdot g)$ for all $g : M$. The conclusion is that the same identity holds for every polynomial: for all $t$ and all $x, y$ in the subtype with $y = \mathrm{act}\,t\,x$, one has $\tau y\,g = \tau x\,(t \cdot g)$ for all $g : M$.
--
--   This is the standard extension-of-identities principle for the free commutative ring $\mathbb{Z}[X_n : n \in \sigma]$ on a set of generators, formulated for a partially defined, non-associative-looking "action" $\mathrm{act}$ on a subset $K$ of a set $E$ together with an additive dictionary $\tau$ into $\mathrm{Hom}(M,R)$: compatibility of $\tau$ with the generators forces compatibility with all polynomial operators. It is used in the construction of the Hecke-equivariant identification of the relevant lattice of points with a group of homomorphisms on a modular curve, where $\sigma$ indexes the abstract Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_forall_apply_eq_apply_smul_of_forall_X_of_eq_act.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial

theorem MvPolynomial.forall_apply_eq_apply_smul_of_forall_X_of_eq_act
    {σ : Type*} {E : Type*} {M : Type*} {R : Type*}
    [AddCommGroup M] [Module (MvPolynomial σ ℤ) M] [AddCommGroup R]
    (K : E → Prop) (mul : E → E → E) (act : MvPolynomial σ ℤ → E → E)
    (hKact : ∀ (t : MvPolynomial σ ℤ) (x : E), K x → K (act t x))
    (hact_mul : ∀ (s t : MvPolynomial σ ℤ) (x : E), K x → act (s * t) x = act t (act s x))
    (hact_add : ∀ (s t : MvPolynomial σ ℤ) (x : E), K x → act (s + t) x = mul (act s x) (act t x))
    (hact_one : ∀ x : E, K x → act 1 x = x)
    (τ : {x : E // K x} → (M →+ R))
    (hτ : ∀ x y z : {x : E // K x}, z.1 = mul x.1 y.1 → τ z = τ x + τ y)
    (hX : ∀ (n : σ) (x y : {x : E // K x}), y.1 = act (X n) x.1 → ∀ g : M, τ y g = τ x ((X n : MvPolynomial σ ℤ) • g)) :
    ∀ (t : MvPolynomial σ ℤ) (x y : {x : E // K x}), y.1 = act t x.1 → ∀ g : M, τ y g = τ x (t • g) := by sorry
