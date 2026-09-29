-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
-- name    : ModularCurve.eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/5455a1d3-3743-50ad-aa77-f5474975eaf7
-- title:
--   Reduction mod ℓ is injective on prime-to-ℓ torsion of J₀(N)
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $\ell$ with $\ell \nmid N$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$, in the sense that the image of $\ell$ in $\overline{\mathbb{Q}}$ belongs to the nonunits of $A$, and write $k_A =$ `IsLocalRing.ResidueField A` for its residue field. Assume [`ModularCurve.ReductionInputsModL A N`](def/ModularCurve_ReductionModL.html#L184), i.e. that for the residue map $A \to k_A$ there exist a map $r$ from the places of the base change to $\overline{\mathbb{Q}}$ of the full level-$N$ modular function field (inside Laurent series) to the places of the corresponding function field over $k_A$ satisfying `IsPlaceReductionAlong`, together with the condition `PrincipalGeneratedByIntegral` for these data. Let $m$ be a natural number with $\ell \nmid m$ (so in particular $m \neq 0$), and let $z$ be an element of [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the group of degree-zero divisor classes modulo principal divisors of that function field over $\overline{\mathbb{Q}}$. If $m \cdot z = 0$ and $z$ is killed by the homomorphism [`ModularCurve.reductionModL A N`](def/ModularCurve_ReductionModL.html#L199) into the degree-zero divisor class group over $k_A$ — the homomorphism attached to a choice of the above data, and the zero map if no such data exist — then $z = 0$.
--
--   This is the injectivity of reduction on the prime-to-$\ell$ torsion of the Jacobian of $X_0(N)$ at a place above a prime $\ell \nmid N$, in the function-field (Deuring) formulation of good reduction used throughout this development; classically it is the statement that reduction of the Néron model of $J_0(N)$, which is an abelian scheme at $\ell \nmid N$, is injective on $m$-torsion for $\ell \nmid m$. It is used when comparing torsion points and their reductions, for instance in the treatment of characteristic-$p$ models of $X_0(N)$, of Frobenius at $\ell$, and in the coefficient estimates for normalised eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero (N : ℕ) [NeZero N] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsModL A N) (m : ℕ) (hm : ¬ ℓ ∣ m) (z : ModularCurve.JZero N)
    (hmz : m • z = 0) (hz : ModularCurve.reductionModL A N z = 0) :
    z = 0 := by sorry
