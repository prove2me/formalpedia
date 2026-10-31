-- Prove2me | Theorems.Thm_OgawaNagaoka_hansen_inequality
-- name    : OgawaNagaoka.hansen_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:16.082991+00:00
-- url     : https://prove2.me/theorems/e9260115-c4ef-4cf2-b04b-aff6811a716b
-- title:
--   Hansen's inequality: $C^*A^\gamma C\le(C^*AC)^\gamma$ for $\|C\|\le1$
-- statement:
--   Let $A$ be a positive semidefinite operator and $C$ an operator with $\|C\|\le1$ on a finite-dimensional Hilbert space, and $0<\gamma\le1$. Then
--
--   $$
--   C^*A^\gamma C\le(C^*AC)^\gamma .
--   $$
--
--   The paper cites it (Hansen [6], [14]) and applies it with a projection and a unitary dilation to prove (18).
--
--   Differences from the source:
--   - reading: operator $A$ (positivity implicit) → hypothesis `A.PosSemidef`; reason: $A^\gamma$ for $0<\gamma\le1$ is meant for a non-negative operator, as in the application where $A$ is block-diagonal with $A_i\ge0$
--   - encoding: $\|C\|\le1$ → `(1 - Cᴴ * C).PosSemidef`; reason: for the operator norm, $\|C\|\le1$ iff $C^*C\le I$
--   - encoding: operators on a Hilbert space (in the application $H\oplus\cdots\oplus H$) → square complex matrices over a finite type; reason: the space is finite dimensional
--   - encoding: operator inequality $X\le Y$ → `(Y - X).PosSemidef`; reason: this is the definition of the Loewner order
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, proof of Lemma 4, p.8

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow

open scoped Matrix ComplexOrder

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, proof of Lemma 4, p.8 (Hansen's inequality, cited from [6], [14]):
for `0 < γ ≤ 1` and operators `A`, `C` with `‖C‖ ≤ 1`, `C* A^γ C ≤ (C* A C)^γ`.

**Formalization Note.** `A` is positive semidefinite (implicit in the paper: `A^γ` is the power of
a non-negative operator). `‖C‖ ≤ 1` (operator norm) is written `I − C*C ⪰ 0`, which is equivalent.
`X ≤ Y` is `(Y - X).PosSemidef`; powers are `matPow`. -/
theorem hansen_inequality {ι : Type} [Fintype ι] [DecidableEq ι] (A C : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hC : (1 - Cᴴ * C).PosSemidef) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (matPow (Cᴴ * A * C) γ - Cᴴ * matPow A γ * C).PosSemidef := by sorry

end OgawaNagaoka
