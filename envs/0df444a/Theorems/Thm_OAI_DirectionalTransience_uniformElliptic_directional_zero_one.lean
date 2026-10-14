-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_uniformElliptic_directional_zero_one
-- name    : OAI.DirectionalTransience.uniformElliptic_directional_zero_one
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-12T18:59:53.266678+00:00
-- url     : https://prove2.me/theorems/6ec03b84-40c7-44e2-b5d3-ab94f89b6e4f
-- title:
--   Zero-one law for directional transience in dimension at least three
-- statement:
--   Let $d\ge3$, let $\nu$ be a uniformly elliptic probability law on transition rows, and let $\ell\ne0$. Then the annealed probability that the i.i.d. random walk in random environment is transient in direction $\ell$ (i.e. $\langle X_n,\ell\rangle\to+\infty$) is either $0$ or $1$.
-- source:
--   OpenAI, openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Probability/Ballisticity/PositiveEscape.lean, lemma `uniformElliptic_directional_zero_one` (line 10), obtained there from the directional zero-one law lean/OAI/Probability/DirectionalWalk (platform theorem `OAI.DirectionalZeroOne.directional_zero_one`) via the row bridge lean/OAI/Probability/Ballisticity/RowBridge.lean. It is used for the velocity hemisphere theorem (lean/OAI/Probability/Ballisticity/VelocityHemisphere.lean) of the manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf.

import Mathlib
import Definitions.Def_VelocityHemisphere

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

theorem uniformElliptic_directional_zero_one {d : ℕ} (hd : 3 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : ℓ ≠ 0) :
    annealedLaw ν (TransientPaths ℓ) = 0 ∨ annealedLaw ν (TransientPaths ℓ) = 1 := by
  sorry

end DirectionalTransience
end OAI
