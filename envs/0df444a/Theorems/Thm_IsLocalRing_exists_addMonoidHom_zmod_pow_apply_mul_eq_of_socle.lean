-- Prove2me | Theorems.Thm_IsLocalRing_exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle
-- name    : IsLocalRing.exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/24c623b8-b1a2-5450-b79f-038649111226
-- title:
--   Extending a socle functional to ℤ/p^N
-- statement:
--   Let $B$ be a finite commutative local ring and $p$ a prime such that the image of $p$ in $B$ lies in the maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal B`. Let $t \in B$ be non-zero and annihilate $\mathfrak m$, i.e. $t\,m = 0$ for every $m \in \mathfrak m$. Then there exists a natural number $N$ with $1 \le N$ and $p^N = 0$ in $B$, having the following property: for every homomorphism $\Lambda$ of additive groups from the residue field $k =$ `IsLocalRing.ResidueField B` to $\mathbb Z/p$ there is a homomorphism $\pi$ of additive groups from $B$ to $\mathbb Z/p^N$ such that, for all $c \in B$,
--   $$\pi(t c) = \overline{\Lambda(\bar c)} \cdot p^{\,N-1} \quad \text{in } \mathbb Z/p^N,$$
--   where $\bar c$ denotes the residue of $c$ in $k$ and $\overline{\Lambda(\bar c)}$ is the canonical natural-number representative of $\Lambda(\bar c) \in \mathbb Z/p$ read in $\mathbb Z/p^N$. Thus $\pi$ restricted to the principal ideal $tB$ is the prescribed functional $\Lambda$ on the socle line, with values in the $p$-torsion subgroup $p^{N-1}\mathbb Z/p^N \cong \mathbb Z/p$, while $\pi$ itself is only required to be additive, not $B$-linear or multiplicative.
--
--   The statement packages the self-injectivity of $\mathbb Z/p^N$ (Baer's criterion) in the form needed to convert an identity read on the socle line $tB \cong k$ of a finite local ring into one with coefficients in $\mathbb Z/p^N$, the residue field functional $\Lambda$ being realised as the restriction of a genuine additive map on all of $B$. It is used in the construction behind [`PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening`](thm.html#PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (t : B) (ht0 : t ≠ 0) (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0) :
    ∃ N : ℕ, 1 ≤ N ∧ (p : B) ^ N = 0 ∧
      ∀ Λ : IsLocalRing.ResidueField B →+ ZMod p, ∃ π : B →+ ZMod (p ^ N),
        ∀ c : B, π (t * c) = ((Λ (IsLocalRing.residue B c)).val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (N - 1) := by sorry
