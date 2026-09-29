-- Prove2me | Theorems.Thm_ModularCurve_hasSum_coeff_eisenstein4_qParam
-- name    : ModularCurve.hasSum_coeff_eisenstein4_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/2aa523d9-9624-5da9-8f4c-5a0edf328bd4
-- title:
--   q-expansion of E₄ converges to E₄(τ)
-- statement:
--   Let $\tau$ be a point of the upper half-plane. The assertion is a `HasSum` statement in $\mathbb{C}$: the family indexed by $m \in \mathbb{N}$ whose $m$-th term is the image in $\mathbb{C}$ of the $m$-th coefficient of the integral power series `eisenstein4`, multiplied by $q^m$ where $q =$ `Function.Periodic.qParam 1 (τ : ℂ)` is the parameter $e^{2\pi i \tau}$ attached to period $1$, is unconditionally summable with sum the value at $\tau$ of Mathlib's level-one weight-four Eisenstein series `ModularForm.E₄`. Here `eisenstein4` is the power series over $\mathbb{Z}$ whose $n$-th coefficient is $1$ for $n = 0$ and $240 \sum_{d \mid n} d^3$ for $n \ge 1$, so the conclusion is the classical identity
--   $$E_4(\tau) = 1 + 240 \sum_{m \ge 1} \sigma_3(m)\, e^{2\pi i m \tau},$$
--   with the convergence recorded in the strong (unordered-sum) form rather than merely as a limit of partial sums.
--
--   This is the $q$-expansion of the weight-four level-one Eisenstein series, in the form of a convergent expansion of the function value rather than an identity of formal series. It is used where the formal $q$-series identities relating $E_4$, the eta product and the $j$- and $\lambda$-invariants must be transported to statements about actual values on the upper half-plane, as in [`ModularCurve.eisenstein4_mul_etaProd_identity`](thm.html#ModularCurve.eisenstein4_mul_etaProd_identity) and its $q$-expansion companions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_coeff_eisenstein4_qParam.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.hasSum_coeff_eisenstein4_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m eisenstein4 : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.E₄ τ) := by sorry
