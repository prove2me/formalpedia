-- Prove2me | Theorems.Thm_GRH_fixed_frequency_escape_iff_squarefull_denominator_tests
-- name    : GRH.fixed_frequency_escape_iff_squarefull_denominator_tests
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T06:03:45.242629+00:00
-- url     : https://prove2.me/theorems/8db95015-bcea-404f-b345-60efe6a50985
-- title:
--   Fixed rational Möbius cancellation is equivalent to squarefull denominator tests
-- statement:
--   Eventual bounds of size (u²+1)^θ for every fixed reduced rational frequency in [0,1) and every 1/2<θ<1 are equivalent to the same tests restricted to squarefull reduced denominators. Denominator 1 is included.
-- source:
--   For the Möbius function, write S_N(x) for the sum of μ(n) exp(2πinx) through N. The bilinear sum B(q,a,N) and the coprime reciprocal sum H_q(U) use the original mission normalizations. Square-cutoff interpolation generalizes the modulus-one prefix estimate at https://prove2.me/submissions/77cbdaf6-d0d3-434d-97b7-ecd2d0125aed to any rational phase.

import Definitions.Def_GRH_SquarefullFrequencies

open Finset GRH.AdditiveMoebiusSpectrum GRH.SquarefullFrequencies

theorem GRH.fixed_frequency_escape_iff_squarefull_denominator_tests : escapes ↔ squarefullTests := by sorry
