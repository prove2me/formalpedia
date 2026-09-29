-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_units_monoidHom_residue_eq
-- name    : IsDiscreteValuationRing.exists_finite_etale_isAdicComplete_units_monoidHom_residue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/5733f38a-d500-5a52-a395-b43e59b5916d
-- title:
--   Finite étale complete DVR extension carrying a Teichmüller character
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring and is complete with respect to the adic topology of its maximal ideal, let $p$ be a prime number whose image in $R$ is irreducible (so $p$ is a uniformiser), and let $F$ be a finite field with $\#F = p^r$ for some $r \neq 0$. The assertion is the existence of a type $R'$ in the same universe as $R$, together with the structure of a commutative ring which is a domain, a discrete valuation ring of characteristic zero, an $R$-algebra that is finite and free as an $R$-module and étale over $R$, such that: $R'$ is complete with respect to the adic topology of its maximal ideal; the structure map $R \to R'$ is a local homomorphism; the image of $p$ in $R'$ is irreducible; $p^r - 1$ is a unit of $R'$; and there exist a monoid homomorphism $\chi : F^\times \to (R')^\times$ and a ring homomorphism $\iota : F \to k_{R'}$ into the residue field of $R'$ with $\overline{\chi(l)} = \iota(l)$ for every $l \in F^\times$, i.e. $\chi$ is a multiplicative lift of $\iota$ restricted to $F^\times$.
--
--   This packages the classical facts that a finite separable residue extension is realised by a finite étale local extension of a complete discrete valuation ring, and that the units of such a ring admit Teichmüller representatives; the coefficient ring $R'$ so produced embeds a prescribed finite field into its residue field together with a character lifting it. It is used in the construction of finite étale Galois extensions of coefficient rings with prescribed $p$-group behaviour, via [`IsDiscreteValuationRing.exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale`](thm.html#IsDiscreteValuationRing.exists_finite_etale_isGalois_isPGroup_commutator_le_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_units_monoidHom_residue_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u w

theorem IsDiscreteValuationRing.exists_finite_etale_isAdicComplete_units_monoidHom_residue_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : R))
    (F : Type w) [Field F] [Fintype F] (r : ℕ) [NeZero r] (hF : Fintype.card F = p ^ r) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : CharZero R')
      (_ : Algebra R R') (_ : Module.Finite R R') (_ : Module.Free R R') (_ : Algebra.Etale R R'),
      IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧ IsLocalHom (algebraMap R R') ∧
      Irreducible (p : R') ∧ IsUnit ((p ^ r : R') - 1) ∧
      ∃ (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R'),
        ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l := by sorry
