-- Prove2me | Theorems.Thm_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization
-- name    : MvPolynomial.formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/6068886f-acf5-5cf7-8265-b098f9c19200
-- title:
--   Localisations of polynomial rings are formally smooth over the base
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, and let $M$ be a submonoid of the polynomial ring $R[x_1,\dots,x_n] =$ `MvPolynomial (Fin n) R`. Let $P$ be a commutative ring equipped with an $R[x_1,\dots,x_n]$-algebra structure making it a localisation of $R[x_1,\dots,x_n]$ at $M$, and with an $R$-algebra structure compatible with the maps $R \to R[x_1,\dots,x_n] \to P$ (a scalar-tower hypothesis). The conclusion is the conjunction of three assertions: $P$ is formally smooth as an $R$-algebra, that is, every $R$-algebra map from $P$ to a quotient $A/I$ by a nilpotent (square-zero) ideal lifts to an $R$-algebra map to $A$; the module of Kähler differentials $\Omega_{P/R}$ is a free $P$-module; and $\Omega_{P/R}$ is a finite $P$-module. Note that the freeness statement is bare freeness together with finiteness: no rank is asserted, although the basis used in the proof is indexed by $\mathrm{Fin}\ n$.
--
--   This is the standard fact that a localisation of an affine space over $R$ is smooth over $R$ with free differentials of rank $n$, here in its formal-smoothness form. It supplies the standing hypotheses `Algebra.FormallySmooth`, `Module.Free` and `Module.Finite` on $\Omega$ needed downstream, and is used by [`MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem`](thm.html#MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial TensorProduct KaehlerDifferential

theorem MvPolynomial.formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P] :
    Algebra.FormallySmooth R P ∧ Module.Free P Ω[P⁄R] ∧ Module.Finite P Ω[P⁄R] := by sorry
