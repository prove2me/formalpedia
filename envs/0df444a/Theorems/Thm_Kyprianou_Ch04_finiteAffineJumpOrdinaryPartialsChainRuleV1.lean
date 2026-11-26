-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteAffineJumpOrdinaryPartialsChainRuleV1
-- name    : Kyprianou.Ch04.finiteAffineJumpOrdinaryPartialsChainRuleV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:32:03.982687+00:00
-- url     : https://prove2.me/theorems/71433cc2-1531-4756-b490-ca1a9e04612e
-- title:
--   Finite affine jump chain rule in ordinary partial derivatives
-- statement:
--   Apply the finite jump telescoping rule on the closed half-plane; split the derivative along affine intervals into the two ordinary partial derivatives. Identify the derivatives away from the Lebesgue-null initial time.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteAffineJumpOrdinaryPartialsChainRuleV1 (S : Finset NNReal) (j : NNReal → ℝ) (d : ℝ)
    (T : NNReal) (hp : ∀ r ∈ S, 0 < r) (hb : ∀ r ∈ S, r ≤ T)
    (f ft fx : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (ft s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fx s x) x)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hft : ContinuousOn (fun z : ℝ × ℝ => ft z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hfx : ContinuousOn (fun z : ℝ × ℝ => fx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    let Y := fun u : ℝ => d*u + ∑ r ∈ S, if (r : ℝ) ≤ u then j r else 0
    let L := fun u : ℝ => d*u + ∑ r ∈ S, if (r : ℝ) < u then j r else 0
    f T (Y T) = f 0 0 + (∫ u in Icc (0 : ℝ) (T : ℝ), ft u (Y u)) +
      d * (∫ u in Icc (0 : ℝ) (T : ℝ), fx u (Y u)) +
      ∑ r ∈ S, (f r (Y r) - f r (L r)) := by
  sorry
end Kyprianou.Ch04
