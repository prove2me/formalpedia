-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_zsmul_eq_pic0_fbar
-- name    : ModularCurve.JHPlaceSpecialization.exists_zsmul_eq_pic0_fbar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/4d8798fd-e65f-5e9a-9be5-8313b2afa8f7
-- title:
--   Divisibility of Pic⁰ of the reduced modular function field
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ and $M/p \neq 0$, and a subgroup $H \le (\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $p$ and is algebraically closed. Let $\mathrm{Fb} =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the field $\mathrm{qExpFunctionFieldC}\,\kappa\,(\Gamma_N(p,M,H))$ of $q$-expansions over $\kappa$ attached to the congruence subgroup `JHNeronObjectAtP.ΓN p M H hpM`, regarded as an extension of $\kappa$. Here $\mathrm{Pic}^0_\kappa(\mathrm{Fb})$ is formed from divisors, i.e. finitely supported $\mathbb{Z}$-valued functions on the places of $\mathrm{Fb}/\kappa$ (valuation subrings of $\mathrm{Fb}$ containing $\kappa$, proper, and principal ideal rings): it is the subgroup of divisors of degree zero modulo those that are principal. Given additionally a place-specialization packet $\mathrm{Psp}$ of type `JHPlaceSpecialization p M H hpM A` (a map on places together with a homomorphism on degree-zero divisor classes and their compatibilities), a nonzero integer $n$, and a class $c \in \mathrm{Pic}^0_\kappa(\mathrm{Fb})$, the assertion is that there exists $c'$ with $n \cdot c' = c$; that is, $\mathrm{Pic}^0_\kappa(\mathrm{Fb})$ is a divisible group.
--
--   This is the standard divisibility of the degree-zero divisor class group of a function field of one variable over an algebraically closed field (the group of points of its Jacobian), here for the function field of the good-reduction fibre at a place above $p$ of the modular curve of level $\Gamma_N(p,M,H)$. It is used in the construction of the specialization homomorphism on divisor classes that glues the characteristic-zero and characteristic-$p$ pictures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_zsmul_eq_pic0_fbar.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.exists_zsmul_eq_pic0_fbar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Psp : JHPlaceSpecialization p M H hpM A)
    (n : ℤ) (hn : n ≠ 0) (c : Pic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :
    ∃ c' : Pic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), n • c' = c := by sorry
