-- Prove2me | Theorems.Thm_IsLocalRing_perfectField_residueField_of_isAlgebraic_rat
-- name    : IsLocalRing.perfectField_residueField_of_isAlgebraic_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/c513ffba-fa60-5b26-8cdd-7a67b415b441
-- title:
--   Perfect residue field of a local subring of ℚ̄
-- statement:
--   Let $L_0$ be a field of characteristic zero that is algebraic over $\mathbb Q$, and let $A_0$ be a local integral domain equipped with an $A_0$-algebra structure on $L_0$ whose structure map $A_0 \to L_0$ is injective; let $p$ be a prime number such that the image of $p$ in $A_0$ lies in the maximal ideal $\mathfrak m_{A_0}$. The conclusion is that the residue field $\kappa(A_0) = A_0/\mathfrak m_{A_0}$, as produced by `IsLocalRing.ResidueField`, is a perfect field, i.e. satisfies the `PerfectField` class. No completeness, noetherianity or valuation hypothesis is imposed on $A_0$, and $L_0$ is not assumed to be a number field; the hypotheses only record that $A_0$ embeds into a field algebraic over $\mathbb Q$ and that its residue characteristic is $p$.
--
--   This is the standard observation that a local subring of an algebraic extension of $\mathbb Q$ has residue field algebraic over $\mathbb F_p$, hence perfect. It is used in the construction of charts on modular curves at full level, where perfectness of a residue field is what feeds the transfer of reducedness to base-changed fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_perfectField_residueField_of_isAlgebraic_rat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.perfectField_residueField_of_isAlgebraic_rat
    (L₀ : Type) [Field L₀] [CharZero L₀] [Algebra.IsAlgebraic ℚ L₀]
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsLocalRing A₀] [Algebra A₀ L₀]
    (hinj : Function.Injective (algebraMap A₀ L₀))
    (p : ℕ) [Fact p.Prime] (hp : (p : A₀) ∈ IsLocalRing.maximalIdeal A₀) :
    PerfectField (IsLocalRing.ResidueField A₀) := by sorry
