-- Prove2me | Theorems.Thm_OAI_GrahamSpherical_full_main
-- name    : OAI.GrahamSpherical.full_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:42.794465+00:00
-- url     : https://prove2.me/theorems/22db9aa3-94b0-45e6-9626-1740bb14a23f
-- statement:
--   The theorem states that a certain explicit set W of twelve points in the Euclidean plane has four properties. Let p = Σ_{m≥0} 10^{-(m+1)!}, u = (1−p²)/(1+p²) and v = 2p/(1+p²), so that (u,v) is a point on the unit circle. Take the four points (1,0), (−1,0), (0,1), (0,−1), and form three labelled copies: the first rotated by the angle with cosine u and sine v, the second rotated by the opposite angle (mapping (x,y) to (ux+vy, −vx+uy)), and the third left unrotated. W is the set of these twelve points, indexed by Fin 3 × Fin 4. The theorem asserts that (1) W has exactly 12 elements, so the points are distinct; (2) W lies on the unit circle centered at the origin; (3) for every positive dimension n there is a colouring of R^n with 50 colours such that no isometric embedding of W into R^n is monochromatic; and (4) W is not Euclidean Ramsey, meaning that it is false that for every positive number r of colours there exists a positive dimension n such that every r-colouring of R^n contains a monochromatic isometric copy of W.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GrahamSpherical.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GrahamSpherical.lean; bytes 1679..1745
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical

namespace OAI

noncomputable section

namespace GrahamSpherical

theorem full_main : Specification.FullAuthoredResult := by
  sorry

end GrahamSpherical
end
end OAI
