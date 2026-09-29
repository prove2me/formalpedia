-- Prove2me | Theorems.Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
-- name    : HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/182bf930-04f4-5356-bf2c-4cf1e7871734
-- title:
--   Finite flat Hopf algebra of order q with cyclotomic points is ℤ_{(q)}[ℤ/q]
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and write $\mathbb{Z}_{(q)}$ for the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $q$. Let $H$ be a commutative ring carrying the structure of a Hopf algebra over $\mathbb{Z}_{(q)}$ which is finite and flat as a $\mathbb{Z}_{(q)}$-module. Assume two conditions on the geometric points of $H$, that is on the $\mathbb{Z}_{(q)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ into an algebraic closure of $\mathbb{Q}$: first, that there are exactly $q$ of them; second, a cyclotomy condition, namely that for every ring automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every natural number $n_\sigma$ such that $\sigma(\zeta) = \zeta^{n_\sigma}$ for all $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^{q} = 1$, every point $\psi$ satisfies $\sigma \circ \psi = \psi^{n_\sigma}$, the power being taken in the convolution monoid structure `WithConv` on the set of points (so that $\sigma(\psi(h))$ agrees with the value at $h$ of the $n_\sigma$-fold convolution power, for all $h \in H$). The conclusion is that the type of bialgebra equivalences over $\mathbb{Z}_{(q)}$ between $H$ and the monoid algebra $\mathbb{Z}_{(q)}[\mathrm{Multiplicative}\,(\mathbb{Z}/q)]$ is nonempty.
--
--   This is the local-at-$q$ form of the classification of finite flat group schemes of order $q$ over $\mathbb{Z}_{(q)}$ in the style of Tate–Oort and Raynaud: a cyclotomic Galois action on the $q$ geometric points forces $\operatorname{Spec} H \cong \mu_q$, equivalently $H \cong \mathbb{Z}_{(q)}[\mathbb{Z}/q]$ as bialgebras. It feeds the corresponding statement over $\mathbb{Z}$, [`HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two`](thm.html#HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two), and the variant [`HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two`](thm.html#HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    (hgenq : Nat.card (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) (h : H),
        σ (ψ h) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) h) :
    Nonempty (H ≃ₐc[GaloisRep.ratLocalizedAt q]
      MonoidAlgebra (GaloisRep.ratLocalizedAt q) (Multiplicative (ZMod q))) := by sorry
