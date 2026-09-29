-- Prove2me | Theorems.Thm_ModularCurve_JOne_smul_heckeOperatorOneBar_and_smul_diamondOneBar
-- name    : ModularCurve.JOne.smul_heckeOperatorOneBar_and_smul_diamondOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/3095522a-3a6d-5534-94cd-c4f692d3f1be
-- title:
--   Galois equivariance of Hecke and diamond operators on J₁(M)
-- statement:
--   Let $M$ be a nonzero natural number and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Write `JOne M` for $\mathrm{Pic}^0$ of the field `x1FunctionFieldBar M`, the base change to $\overline{\mathbb{Q}}$ of the function field `x1FunctionField M` inside the Laurent series field, that is, the quotient of the group of degree-zero divisors by the subgroup of principal divisors; the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ acts on `JOne M` by a `DistribMulAction` coming from the coefficientwise action on places and divisors. The theorem asserts the conjunction of two commutation statements. First, for every prime $\ell$ and every $x \in$ `JOne M`, $\sigma \bullet (T_\ell x) = T_\ell(\sigma \bullet x)$, where $T_\ell$ is `heckeOperatorOneBar M ℓ`, the $\mathbb{Z}$-linear endomorphism of `JOne M` underlying `heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ` (the endomorphism built from the Hecke data via `heckePic0OneBar` when `HeckeInputsOneAlong` holds, and zero otherwise). Second, for every natural number $d$ and every $x$, $\sigma \bullet (\langle d\rangle x) = \langle d\rangle(\sigma \bullet x)$, where $\langle d\rangle$ is `diamondOneBar M d`, the $\mathbb{Z}$-linear endomorphism given by the action of the semilinear automorphism attached to `diamondAutBar M d`, the base change to $\overline{\mathbb{Q}}$ of the diamond automorphism `diamondAut M d` of the function field.
--
--   This is the statement that the Hecke operators $T_\ell$ and the diamond operators $\langle d\rangle$ on the $\overline{\mathbb{Q}}$-points of the Jacobian of $X_1(M)$ are defined over $\mathbb{Q}$, hence commute with the action of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$. It is used in the construction of the Galois-equivariant comparison between Hecke-module structures and the Abel–Jacobi map on the two-chart model of $X_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_smul_heckeOperatorOneBar_and_smul_diamondOneBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.smul_heckeOperatorOneBar_and_smul_diamondOneBar
    (M : ℕ) [NeZero M] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (∀ (ℓ : Nat.Primes) (x : ModularCurve.JOne M),
        σ • ModularCurve.heckeOperatorOneBar M ℓ x = ModularCurve.heckeOperatorOneBar M ℓ (σ • x)) ∧
    (∀ (d : ℕ) (x : ModularCurve.JOne M),
        σ • ModularCurve.diamondOneBar M d x = ModularCurve.diamondOneBar M d (σ • x)) := by sorry
