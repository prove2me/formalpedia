-- Prove2me | Theorems.Thm_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
-- name    : MvFormalGroup.Hom.exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/7421a5b9-5797-5503-b12a-ae7c919eaacc
-- title:
--   Factoring an isogeny of formal groups through Frobenius
-- statement:
--   Let $p$ be a prime and $k$ a field of characteristic $p$, let $d$ be a natural number, and let $\Psi,\Phi$ be $d$-dimensional formal group laws over $k$, i.e. $d$-tuples of power series in the variables indexed by $\mathrm{Fin}\,d\oplus\mathrm{Fin}\,d$ with vanishing constant term, linear part $X_i+Y_i$ and the associativity identity, both assumed commutative in the sense that interchanging the two blocks of variables fixes each component. Let $\psi\colon\Psi\to\Phi$ be a homomorphism: a $d$-tuple $\psi_i$ of power series in $d$ variables with zero constant term satisfying $\psi(\Psi(X,Y))=\Phi(\psi(X),\psi(Y))$. Assume the kernel algebra $k[[X_1,\dots,X_d]]/(\psi_1,\dots,\psi_d)$ is a finite $k$-module. Then there exist a commutative $d$-dimensional formal group law $\Psi'$ over $k$ and homomorphisms $\pi\colon\Psi\to\Psi'$, $\rho\colon\Psi'\to\Psi^{(p)}$, where $\Psi^{(p)}$ is obtained from $\Psi$ by applying the Frobenius endomorphism of $k$ to all coefficients, and $\psi'\colon\Psi'\to\Phi$, such that componentwise $\psi'\circ\pi=\psi$ and the $i$-th component of $\rho\circ\pi$ is $X_i^p$; writing $s$ for the rank of the matrix of degree-one coefficients of $\psi$ and $r=d-s$ (truncated subtraction of naturals), the corresponding matrix for $\rho$ has rank $r$, the kernel algebra of $\pi$ has $k$-dimension $p^r$, the kernel algebras of $\rho$ and of $\psi'$ are finite over $k$, and $\dim_k k[[X]]/(\psi)=p^r\cdot\dim_k k[[X]]/(\psi')$.
--
--   This is the construction of the quotient of a formal group law by the part of the kernel of an isogeny killed by Frobenius: $\Psi'=\Psi/(\ker\psi\cap\Psi[F])$, with the multiplicativity of degrees in the factorisation $\psi=\psi'\circ\pi$. It is used in the Cartier-module analysis of isogenies of formal groups, in particular in the results computing lengths, bases and Verschiebung-iterates of quotients whose degree is a power of $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.Hom.exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ)
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries))) :
    ∃ (Ψ' : MvFormalGroup d k) (_ : Ψ'.IsComm) (π : Ψ.Hom Ψ')
      (ρ : Ψ'.Hom (Ψ.map (frobenius k p))) (ψ' : Ψ'.Hom Φ),
      (∀ i, (ψ'.comp π).toPowerSeries i = ψ.toPowerSeries i) ∧
      (∀ i, (ρ.comp π).toPowerSeries i = (X i : MvPowerSeries (Fin d) k) ^ p) ∧
      (MvFormalGroup.linearPart ρ.toPowerSeries).rank =
        d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank ∧
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range π.toPowerSeries)) =
        p ^ (d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank) ∧
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ρ.toPowerSeries)) ∧
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) ∧
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) =
        p ^ (d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank) *
          Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) := by sorry
