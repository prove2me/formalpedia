-- Prove2me | Theorems.Thm_IsRegularLocalRing_exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero
-- name    : IsRegularLocalRing.exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/3f408fd5-b69a-5476-aa2c-3ac0d241fd51
-- title:
--   Complete regular local ring of dimension ≤ 2 maps to a complete DVR
-- statement:
--   Let $R_y$ be a commutative ring that is regular local, with $\operatorname{ringKrullDim} R_y \le 2$, and complete (in the sense of `IsAdicComplete`) for its maximal ideal $\mathfrak m$. Let $p$ be a prime number such that the image of $p$ in $R_y$ is nonzero, and let $k$ be an algebraically closed field of characteristic $p$. Assume given a ring homomorphism $\iota_0 : R_y/\mathfrak m^{0+1} \to k$ (the exponent $0+1$ means that the source is the residue field $R_y/\mathfrak m$) which is bijective, so that $k$ is identified with the residue field of $R_y$. The assertion is that there exist a type $R$ carrying a commutative ring structure, which is a domain, a discrete valuation ring and of characteristic zero, together with ring homomorphisms $\psi : R_y \to R$ and $\varphi : R \to k$, such that $\varphi$ is surjective, $R$ is complete for its maximal ideal, and $\varphi \circ \psi$ equals the composite of the quotient map $R_y \to R_y/\mathfrak m^{0+1}$ followed by $\iota_0$.
--
--   This is the passage from a deformation hull of Krull dimension at most $2$ to a complete characteristic-zero discrete valuation ring with algebraically closed residue field $k$, compatibly with the residue map. It is used in the construction of fake elliptic curves over such a ring in the Čerednik–Drinfeld part of the development, where a pullback square over a complete DVR of characteristic $0$ is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero
    (Ry : Type) [CommRing Ry] [IsRegularLocalRing Ry] (hd : ringKrullDim Ry ≤ 2) [IsAdicComplete (maximalIdeal Ry) Ry]
    (p : ℕ) [Fact p.Prime] (hp : ((p : ℕ) : Ry) ≠ 0)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (ι₀ : (Ry ⧸ maximalIdeal Ry ^ (0 + 1)) →+* k) (hι₀ : Function.Bijective ι₀) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : CharZero R)
      (ψ : Ry →+* R) (φ : R →+* k),
      Function.Surjective φ ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      φ.comp ψ = ι₀.comp (Ideal.Quotient.mk (maximalIdeal Ry ^ (0 + 1))) := by sorry
