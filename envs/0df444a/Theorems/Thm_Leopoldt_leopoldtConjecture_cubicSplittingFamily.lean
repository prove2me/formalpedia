-- Prove2me | Theorems.Thm_Leopoldt_leopoldtConjecture_cubicSplittingFamily
-- name    : Leopoldt.leopoldtConjecture_cubicSplittingFamily
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-23T06:01:47.20243+00:00
-- url     : https://prove2.me/theorems/8b77a8a7-0e07-4428-b6eb-f0908176f05c
-- title:
--   Leopoldt's conjecture for the splitting fields of $X^3-t^2X-1$
-- statement:
--   Let $t\ge2$ be an integer and let $p$ be an odd prime dividing $t$. Leopoldt's conjecture holds at $p$ for the splitting field of $X^3-t^2X-1$ over $\mathbb Q$.
-- source:
--   Ferri and Johnston, Applications of representation theory and of explicit units to Leopoldt’s conjecture, Theorem 6.5 for p ≥ 5, https://doi.org/10.1007/s40993-026-00717-2. The accompanying proof also treats p = 3 by a separate local logarithm calculation.

import Definitions.Def_LeopoldtDefect
import Mathlib.FieldTheory.SplittingField.Construction

set_option autoImplicit false
open NumberField

theorem Leopoldt.leopoldtConjecture_cubicSplittingFamily
    (t : ℕ) (ht : 2 ≤ t) (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hdiv : p ∣ t) :
    let K := (Polynomial.X ^ 3 - Polynomial.C ((t : ℚ) ^ 2) * Polynomial.X - 1).SplittingField
    letI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
    Leopoldt.LeopoldtConjecture p K := by sorry
