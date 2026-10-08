-- Prove2me | Theorems.Thm_Helfgott_weighted_count_lower
-- name    : Helfgott.weighted_count_lower
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-04T21:26:31.199866+00:00
-- url     : https://prove2.me/theorems/ff869c8e-3ec2-4fe1-883d-1da7774dfa4a
-- title:
--   Helfgott weighted lower bound in the analytic range
-- statement:
--   For every odd N≥10²⁷, choose x=N/(2+9/(196√(2π))). The finite von Mangoldt weighted ternary count with the actual coordinated smoothings η+,η* is at least N²/2500. This is a weaker consequence of the paper’s major-arc lower bound and minor-arc upper bound after the circle-method counting identity; those analytic estimates and their computational inputs remain to be proved. This theorem is the outstanding analytic input, not an assumed fact in a direct Goldbach proof.
-- source:
--   Helfgott, arXiv:1312.7748v2, equations (7.14), (7.25), (7.48) and (7.49)–(7.50); the weaker rational threshold N²/2500 is derived from the concluding bound 0.00042248N². https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_PrimePowerRemoval
open scoped BigOperators

namespace Helfgott

theorem weighted_count_lower (N : ℕ) (hN : 10 ^ 27 ≤ N) (hodd : Odd N) :
    let x : ℝ := (N : ℝ) / (2 + 9 / (196 * Real.sqrt (2 * Real.pi)))
    (1 / 2500 : ℝ) * (N : ℝ)^2 ≤
      ∑ t ∈ tripleIndices N,
        weightedTripleTerm (fun n => etaPlus ((n : ℝ) / x))
          (fun n => etaStar ((n : ℝ) / x)) t := by sorry

end Helfgott
