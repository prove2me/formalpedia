-- Prove2me | Theorems.Thm_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
-- name    : ModularCurve.meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/416a532b-c720-58ab-9911-d53629fcd33d
-- title:
--   Order of j-j(τ) equals half the stabiliser order
-- statement:
--   Let $\tau$ be a point of the upper half-plane $\mathbb{H}$. Consider the function of a complex variable $z$ given by $E_4(\mathrm{ofComplex}\,z)^3/\Delta(\mathrm{ofComplex}\,z) - E_4(\tau)^3/\Delta(\tau)$, where $E_4$ is the normalised weight-$4$ Eisenstein series `ModularForm.E₄` for $\mathrm{SL}_2(\mathbb{Z})$, $\Delta$ is `ModularForm.discriminant`, and `ofComplex` is the map $\mathbb{C}\to\mathbb{H}$ which is the identity on the upper half-plane (and constant off it); thus near $\tau$ the function is $j(z)-j(\tau)$ for the modular invariant $j=E_4^3/\Delta$. The assertion is that the meromorphic order of this function at the point $\tau$, viewed in $\mathbb{C}$, equals the integer obtained from the natural number $\#\mathrm{Stab}_{\mathrm{SL}_2(\mathbb{Z})}(\tau)/2$, the quotient being natural-number division of the cardinality of the stabiliser of $\tau$ for the action of $\mathrm{SL}_2(\mathbb{Z})$ on $\mathbb{H}$. Since `meromorphicOrderAt` takes values in $\mathbb{Z}\cup\{\infty\}$, the equality with a finite value also records that $j-j(\tau)$ does not vanish identically near $\tau$. As the stabiliser contains $\pm 1$ and has order $2$, $4$ or $6$, the right-hand side is $1$, $2$ or $3$, namely $1$ away from the elliptic points and $2$, resp. $3$, at points equivalent to $i$, resp. to $e^{2\pi i/3}$.
--
--   This is the classical computation of the multiplicity with which the modular invariant $j$ attains the value $j(\tau)$, the multiplicity being the ramification index $e_\tau$ of $\mathbb{H}\to\mathbb{H}/\mathrm{SL}_2(\mathbb{Z})$ at $\tau$. It feeds the identification of ramification indices of maps of modular curves, used in the results relating ramification to stabiliser orders for $\mathrm{SL}_2(\mathbb{Z})$ and for $\Gamma_1$-level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
    (τ : ℍ) :
    meromorphicOrderAt
        (fun z : ℂ => (ModularForm.E₄ : ℍ → ℂ) (ofComplex z) ^ 3 /
            ModularForm.discriminant (ofComplex z)
          - (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) (τ : ℂ) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := by sorry
