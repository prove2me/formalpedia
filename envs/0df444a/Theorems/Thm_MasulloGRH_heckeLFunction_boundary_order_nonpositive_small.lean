-- Prove2me | Theorems.Thm_MasulloGRH_heckeLFunction_boundary_order_nonpositive_small
-- name    : MasulloGRH.heckeLFunction_boundary_order_nonpositive_small
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T20:00:25.557185+00:00
-- url     : https://prove2.me/theorems/dc771b50-4ddf-4a1b-918b-4b0c9a198a4f
-- title:
--   Boundary nonvanishing for finite Hecke L-functions in the small-field representation
-- statement:
--   For every number field $F$ whose carrier lies in Lean’s universe $\mathrm{Type}\,0$, every continuous unitary character $\chi$ of its idele class group, and every real $t$, the meromorphic order of the MasulloGRH finite Hecke $L$-function at $1+it$ is at most zero. Thus it has no zero at any point of the line $\Re s=1$ in this representation. A negative order records a genuine pole even though the normal-form representative takes the value zero there. No hypothesis on the square of $\chi$ or on the height $t$ is needed.
-- source:
--   Masullo, The Music of the Primes, Appendix B.6.1. Unconditional smallest-universe instance of 4097fa76-f445-47f5-920e-ef638f3476cd on Re(s)=1 and strengthening of the 4833ae58-2732-4e3a-9980-79c29db50fc2 square-character-pole case. Transfers the independently proved Tate theorem ecb98452-c4d2-5b41-b576-000133eadaa1 through equality of the actual local characters and their Euler coefficients.

import Definitions.Def_MasulloGRH_HeckeLFunction
open MasulloGRH

theorem MasulloGRH.heckeLFunction_boundary_order_nonpositive_small (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F) (t : ℝ) :
    meromorphicOrderAt (heckeLFunction χ) (1 + (t : ℂ) * Complex.I) ≤ 0 := by sorry
