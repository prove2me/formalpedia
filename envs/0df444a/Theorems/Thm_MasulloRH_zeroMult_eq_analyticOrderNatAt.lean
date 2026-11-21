-- Prove2me | Theorems.Thm_MasulloRH_zeroMult_eq_analyticOrderNatAt
-- name    : MasulloRH.zeroMult_eq_analyticOrderNatAt
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:03:37.35739+00:00
-- url     : https://prove2.me/theorems/f402345a-0d4d-46a8-8ca1-865faac376c9
-- title:
--   Bridge lemma: the Connes multiplicity of a zeta zero is its analytic order
-- statement:
--   The spectral side of the Weil explicit formula, as formalized in the module `ConnesRZ_weil_defs`, weights each zero $s$ of the Riemann zeta function by the multiplicity `ConnesRZ.zeroMult s`. The Masullo trace-formula nodes, in contrast, weight zeros by Mathlib's analytic order `analyticOrderNatAt riemannZeta s`. This lemma records that the two weights coincide for every complex number $s$:
--
--   $$\mathrm{zeroMult}(s) = \mathrm{ord}_s(\zeta).$$
--
--   In fact the identification is definitional: `ConnesRZ.zeroMult` is defined to be the analytic order of `riemannZeta`. Stating it as a named theorem removes the definitional friction between the two families of nodes, so that spectral sums written with `zeroMult` (for instance the omitted-zero sums in the MasulloRH trace window) can be rewritten with `analyticOrderNatAt` (as in `MasulloRH.zetaTraceTerm`) and conversely, without unfolding definitions at each use site.
-- source:
--   Platform definition module ConnesRZ_weil_defs (Connes, 'Trace formula in noncommutative geometry and the zeros of the Riemann zeta function', section 3, case k = Q), definition of zeroMult; mission 'Masullo: The Music of the Primes — Riemann Hypothesis specialization', MasulloRH_RationalTrace definitions.

import Definitions.Def_ConnesRZ_weil_defs

theorem MasulloRH.zeroMult_eq_analyticOrderNatAt (s : ℂ) : ConnesRZ.zeroMult s = analyticOrderNatAt riemannZeta s := by sorry
