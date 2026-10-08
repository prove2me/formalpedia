-- Prove2me | Theorems.Thm_OAI_HyperbolicObstruction_main
-- name    : OAI.HyperbolicObstruction.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:45.684062+00:00
-- url     : https://prove2.me/theorems/6c46d445-40a6-465c-82c5-ea86732775ae
-- statement:
--   The theorem states that the defined proposition MainStatement holds, namely that there exist a finite abstract simplicial complex K on vertices Fin n, with its standard barycentric realization |K| (nonnegative coordinate vectors summing to 1 supported on a face), a basepoint x in |K|, and a real constant C ≥ 0 such that all of the following hold. |K| is connected and aspherical at x, meaning every homotopy group π_{m}(|K|,x) with m ≥ 2 is trivial. K satisfies a linear disk-filling inequality: every closed edge path p that bounds some disk, where a disk is a chain of elementary moves (collapsing a repeated vertex, removing a spur a,b,a, or replacing a,b,c by a,c across a nondegenerate triangular face, which costs one) reducing p to a single vertex, admits such a disk using at most C times (length of p minus 1) triangular faces. The fundamental group G = π₁(|K|,x) is word hyperbolic in the four-point sense: for some finite generating set S and some δ ≥ 0, every a,b,c,d in G satisfy d(a,c)+d(b,d) ≤ max(d(a,b)+d(c,d), d(a,d)+d(b,c)) + 2δ, where d is word distance. G admits no geometric CAT(0) action: there is no proper cocompact isometric action of G on any nonempty proper complete metric space X (in universe u) that is CAT(0), in the sense that segments exist with the squared-distance comparison inequality. Finally, for every finite complex L whose realization is homotopy equivalent to |K|, there is no metric on |L|, inducing its given topology, that is geodesic and locally CAT(−1), meaning each point has a ball that satisfies the hyperbolic-cosine midpoint inequality cosh d(z,m) ≤ (cosh d(z,x)+cosh d(z,y))/(2cosh(d(x,y)/2)) for segment midpoints m.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HyperbolicObstruction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HyperbolicObstruction.lean; bytes 6196..6240
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HyperbolicObstruction

namespace OAI

section

section

noncomputable section

open scoped Topology ContinuousMap

namespace HyperbolicObstruction

universe u

theorem main : MainStatement.{u} := by sorry

end HyperbolicObstruction
end
end
end
end OAI
