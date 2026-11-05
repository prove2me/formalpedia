-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_properlyInfiniteVanishingInput
-- name    : OAI.BoundedHochschild.KadisonRingrose.properlyInfiniteVanishingInput
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:09.980234+00:00
-- url     : https://prove2.me/theorems/0611e9e5-7cb0-48db-9dc4-25d864423442
-- title:
--   Vanishing of bounded cohomology with no finite central summand
-- statement:
--   For every unital C*-algebra $N$ with star-ordered partial order that is a W*-algebra (`WStarAlgebra N`) and has no finite central summand (a central projection whose corner is finite vanishes, `NoFiniteCentralSummand N`), and every $n$, each bounded Hochschild cocycle $f$ of degree $n+2$ on $N$ with values in $N$ has a bounded primitive: there is a bounded cochain $g$ of degree $n+1$ with $\partial g=f$. This is the proposition `ProperlyInfiniteVanishingInput`, stated for a fixed universe level. Here a cochain of degree $k$ is a bounded complex $k$-linear map $N^k\to N$, and $\partial$ (`differentialValue`) is the Hochschild differential $(\partial f)(v_0,\dots,v_k)=v_0f(v_1,\dots,v_k)+\sum_{j<k}(-1)^{j+1}f(\dots,v_jv_{j+1},\dots)+(-1)^{k+1}f(v_0,\dots,v_{k-1})v_k$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.properlyInfiniteVanishingInput`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/ProperlyInfinitePrimitives.lean#L35

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem properlyInfiniteVanishingInput : ProperlyInfiniteVanishingInput.{u} := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
