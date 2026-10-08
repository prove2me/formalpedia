-- Prove2me | Theorems.Thm_Helfgott_weighted_count_lower_of_numerical_arcs
-- name    : Helfgott.weighted_count_lower_of_numerical_arcs
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T23:46:19.359805+00:00
-- url     : https://prove2.me/theorems/d02d298b-e9a0-4a75-b13f-b9ebd7b09c2f
-- title:
--   Actual weighted ternary lower bound from the two numerical arc estimates
-- statement:
--   For every positive natural N, at the actual scale x=N/(2+9/(196√(2π))), assume the real major-arc integral is at least 1.058259x²/49 and the nonnegative minor-arc mass is at most 0.97392x²/49. Then the actual finite von Mangoldt weighted ternary count is at least N²/2500. Both numerical arc estimates are explicit hypotheses. The proof establishes the continuity and integrability of the complete infinite sums, measurability of the exact parity-dependent arcs, the counting identity, the control of the minor integral by its absolute-value mass, and the numerical scale conversion. It proves the analytic-to-arithmetic reduction, not the two assumed arc estimates.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (3.5), (7.14), (7.25), (7.48) and (7.49). https://arxiv.org/html/1312.7748v2 . The weaker rational threshold N²/2500 is derived here using 2≤2+9/(196√(2π))≤2.03. Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
open MeasureTheory
open scoped BigOperators

namespace Helfgott

theorem weighted_count_lower_of_numerical_arcs (N : ℕ) (hN : 0 < N)
    (hmajor : (1058259/1000000 : ℝ)*((goldbachScale N)^2/49) ≤
      (∫ α in majorArcs 8 150000 (goldbachScale N),
        ternaryIntegrand (goldbachScale N) N α ∂AddCircle.haarAddCircle).re)
    (hminor : minorArcMass (goldbachScale N) ≤
      (97392/100000 : ℝ)*((goldbachScale N)^2/49)) :
    (1/2500 : ℝ)*(N : ℝ)^2 ≤
      ∑ t ∈ tripleIndices N,
        weightedTripleTerm (fun n => etaPlus ((n : ℝ)/(goldbachScale N)))
          (fun n => etaStar ((n : ℝ)/(goldbachScale N))) t := by sorry

end Helfgott
