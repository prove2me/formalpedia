-- Prove2me | Theorems.Thm_GRH_moebius_square_cutoff_power_bounds_at_squarefull_denominators
-- name    : GRH.moebius_square_cutoff_power_bounds_at_squarefull_denominators
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-27T06:03:26.672354+00:00
-- url     : https://prove2.me/theorems/20ac04ac-e747-5680-a741-ed0d2b66dc1b
-- title:
--   Möbius power bounds at square cutoffs for each squarefull denominator
-- statement:
--   For every fixed squarefull q>0 and reduced a/q in [0,1), for every exponent θ strictly between one half and one, prove that |S_{u²}(a/q)|≤(u²+1)^θ for all sufficiently large u. The starting index may depend on q, a and θ.
-- source:
--   For the Möbius function, write S_N(x) for the sum of μ(n) exp(2πinx) through N. The bilinear sum B(q,a,N) and the coprime reciprocal sum H_q(U) use the original mission normalizations.

import Definitions.Def_GRH_SquarefullFrequencies

theorem GRH.moebius_square_cutoff_power_bounds_at_squarefull_denominators :
    GRH.SquarefullFrequencies.squarefullTests := by sorry
