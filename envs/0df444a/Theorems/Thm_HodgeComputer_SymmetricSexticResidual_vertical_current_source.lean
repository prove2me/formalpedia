-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_vertical_current_source
-- name    : HodgeComputer.SymmetricSexticResidual.vertical_current_source
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-16T05:48:24.413736+00:00
-- url     : https://prove2.me/theorems/d2b7bf83-4bd7-4977-b3c4-73ad2c4a8c9e
-- title:
--   Symmetric sextic: vertical current divergence on the cubic cover
-- statement:
--   Let $K$ be a field of characteristic zero equipped with an additive derivation $T : K \to K$. Suppose $t, u, \ell, B, C, D, B_x, C_x, D_x \in K$ satisfy the curve relation $\ell u^3 + B u^2 + C u + D = 0$, $\ell \neq 0$, $g := 3\ell u^2 + 2 B u + C \neq 0$, and the implicit chain-rule identities $T(t) = 1$, $T(\ell) = 0$, $T(B) = 2 t B_x$, $T(C) = 2 t C_x$, and $T(u) = -2 t (B_x u^2 + C_x u + D_x) / g$. Setting $x = t^2$, $g_u = 6\ell u + 2 B$, and
--
--   $$K_0 = \frac{-BC + 4 x B_x C + 9\ell D - 12\ell x D_x}{12\ell}, \qquad K_1 = \frac{-B^2 + 4 x B B_x + 3\ell C - 6\ell x C_x}{6\ell},$$
--
--   we have the exact vertical-current source identity
--
--   $$T\!\left(\frac{t}{g}\right) = \frac{2\bigl(g K_1 - g_u (K_0 + K_1 u)\bigr)}{g^3}.$$
--
--   This shows that adding a time-constant multiple $a \in \ker T$ of $t/g$ shifts the canonical linear source coefficients by $a(K_0, K_1)$, reducing the seven selector moment equations to six.
-- source:
--   https://github.com/hodge-computer/sextics/discussions/117#discussioncomment-19498520 (symmetric-contact-current/source/selector/REMOVABLE_SELECTOR_MOMENT.md)

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem HodgeComputer.SymmetricSexticResidual.vertical_current_source
    {K : Type*} [Field K] [CharZero K]
    (T : Derivation ℤ K K) (t u l B C D Bx Cx Dx : K)
    (hTt : T t = 1) (hTl : T l = 0)
    (hTB : T B = 2 * t * Bx) (hTC : T C = 2 * t * Cx)
    (hTu : T u = -(2 * t * (Bx * u ^ 2 + Cx * u + Dx)) / (3 * l * u ^ 2 + 2 * B * u + C))
    (hl : l ≠ 0)
    (hf : l * u ^ 3 + B * u ^ 2 + C * u + D = 0)
    (hg : 3 * l * u ^ 2 + 2 * B * u + C ≠ 0) :
    let x := t ^ 2
    let g := 3 * l * u ^ 2 + 2 * B * u + C
    let gu := 6 * l * u + 2 * B
    let K0 := (-B * C + 4 * x * Bx * C + 9 * l * D - 12 * l * x * Dx) / (12 * l)
    let K1 := (-B ^ 2 + 4 * x * B * Bx + 3 * l * C - 6 * l * x * Cx) / (6 * l)
    T (t / g) = 2 * (g * K1 - gu * (K0 + K1 * u)) / g ^ 3 := by sorry
