-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_ballistic_of_almost_sure_transience
-- name    : OAI.DirectionalTransience.ballistic_of_almost_sure_transience
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-12T19:00:49.420126+00:00
-- url     : https://prove2.me/theorems/ad4bfc68-896e-489a-a077-d494aef1b2da
-- title:
--   Directional transience implies ballisticity (unit direction, velocity-hemisphere vocabulary)
-- statement:
--   Let $d\ge2$ and let $\nu$ be a uniformly elliptic probability law on transition rows. Let $\ell\in\mathbb R^d$ be a unit vector ($\ell\cdot\ell=1$). Suppose the i.i.d. random walk in random environment is **directionally transient** in direction $\ell$: under the annealed law, $\langle X_n,\ell\rangle\to+\infty$ with probability one. Then there is a vector $v$ with $v\cdot\ell>0$ such that $X_n/n\to v$ with annealed probability one.
--
--   This is the main theorem of the manuscript, stated with the definitions of the `VelocityHemisphere` group (events `TransientPaths`, `VelocityPaths` of annealed probability one). The mission goal `OAI.DirectionalTransience.directional_transience_implies_ballisticity` states the same result with the separate `DirectionalBallisticity` definitions, which cannot be imported together with these.
-- source:
--   OpenAI, *Directional transience implies ballisticity*, preprint, September 2026 (https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf), main theorem. Lean: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Probability/Ballisticity/Renewal/VelocityWords.lean, theorem `directional_transience_implies_ballisticity_unit` (line 152), restated with the event definitions of lean/ComparatorChallenges/VelocityHemisphere.lean.

import Mathlib
import Definitions.Def_VelocityHemisphere

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

theorem ballistic_of_almost_sure_transience {d : ℕ} (hd : 2 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : annealedLaw ν (TransientPaths ℓ) = 1) :
    ∃ v : Vector d, 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 := by
  sorry

end DirectionalTransience
end OAI
