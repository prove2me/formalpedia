-- Prove2me | Theorems.Thm_Leopoldt_leopoldtConjecture_cmCubicSplittingFamily
-- name    : Leopoldt.leopoldtConjecture_cmCubicSplittingFamily
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-23T06:01:42.390852+00:00
-- url     : https://prove2.me/theorems/a976357c-429b-458c-8abd-dacc3946daf0
-- title:
--   Leopoldt's conjecture for the CM fields from $(X^3-t^2X-1)(X^2+1)$
-- statement:
--   Let $t\ge2$ be an integer and let $p$ be an odd prime dividing $t$. Leopoldt's conjecture holds at $p$ for the splitting field of $(X^3-t^2X-1)(X^2+1)$ over $\mathbb Q$. This field is a degree-$12$ CM extension of $\mathbb Q$ whose maximal real subfield is the splitting field of $X^3-t^2X-1$.
-- source:
--   Ferri and Johnston, Applications of representation theory and of explicit units to Leopoldt’s conjecture, Theorem 6.5 for p ≥ 5, https://doi.org/10.1007/s40993-026-00717-2. The accompanying proof also treats p = 3 by a separate local logarithm calculation.

import Definitions.Def_LeopoldtDefect
import Mathlib.FieldTheory.SplittingField.Construction

set_option autoImplicit false
open NumberField

theorem Leopoldt.leopoldtConjecture_cmCubicSplittingFamily
    (t : ℕ) (ht : 2 ≤ t) (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hdiv : p ∣ t) :
    let K := ((Polynomial.X ^ 3 - Polynomial.C ((t : ℚ) ^ 2) * Polynomial.X - 1) * (Polynomial.X ^ 2 + 1)).SplittingField
    letI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
    Leopoldt.LeopoldtConjecture p K := by sorry
