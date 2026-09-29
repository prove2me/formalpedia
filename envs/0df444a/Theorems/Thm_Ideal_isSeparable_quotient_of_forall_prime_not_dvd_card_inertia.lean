-- Prove2me | Theorems.Thm_Ideal_isSeparable_quotient_of_forall_prime_not_dvd_card_inertia
-- name    : Ideal.isSeparable_quotient_of_forall_prime_not_dvd_card_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/4699ea0c-c33a-5df8-bcfe-d025f247555b
-- title:
--   Residue separability from inertia of order prime to the residue characteristic
-- statement:
--   Let $R$ and $S$ be commutative rings which are Dedekind domains, with $S$ an $R$-algebra that is finite and torsion-free as an $R$-module, and let $G$ be a finite group acting on $S$ by ring automorphisms in such a way that $G$ is a Galois group for the extension $R \to S$ in the sense of Mathlib's `IsGaloisGroup` (so in particular $R$ is the ring of $G$-invariants of $S$). Let $p$ be a maximal ideal of $R$ with $p \neq \bot$, and let $P$ be a maximal ideal of $S$ lying over $p$. Assume that for every natural prime $\ell$ whose image in the residue field $R/p$ is zero, $\ell$ does not divide $\operatorname{card}$ of the inertia subgroup $P.\mathrm{inertia}\ G$ of $P$ in $G$ (equivalently: the residue characteristic, when positive, is prime to the order of the inertia group). Then the residue field extension $S/P$ is separable over $R/p$.
--
--   This is the standard criterion identifying tame inertia with separable residue extensions: for a Galois cover of Dedekind domains one has $|I_P| = e(P\mid p)\cdot[S/P : R/p]_{\mathrm{insep}}$, so an inertia group of order prime to the residue characteristic forces the residue extension to be separable. It is the converse companion of the Mathlib result computing $|I_P|$ as the ramification index under an assumed separability hypothesis, and it is used in the proof of [`Algebra.IsInvariant.isSeparable_of_isFractionRing_quotient_of_lt_of_isUnit_card_inertia`](thm.html#Algebra.IsInvariant.isSeparable_of_isFractionRing_quotient_of_lt_of_isUnit_card_inertia).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_isSeparable_quotient_of_forall_prime_not_dvd_card_inertia.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.isSeparable_quotient_of_forall_prime_not_dvd_card_inertia
    {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (hI : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : R ⧸ p) = 0 → ¬ ℓ ∣ Nat.card ↥(P.inertia G)) :
    Algebra.IsSeparable (R ⧸ p) (S ⧸ P) := by sorry
