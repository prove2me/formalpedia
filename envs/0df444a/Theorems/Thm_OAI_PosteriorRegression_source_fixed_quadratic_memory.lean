-- Prove2me | Theorems.Thm_OAI_PosteriorRegression_source_fixed_quadratic_memory
-- name    : OAI.PosteriorRegression.source_fixed_quadratic_memory
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:33:24.86486+00:00
-- url     : https://prove2.me/theorems/832f17fd-608b-4e92-a5c3-5a7f6796c0e7
-- title:
--   A seeded learner with M ≤ A d² bits and success 2/3 needs T ≥ d log(1/ε)/(4(400000 + 100A)) samples (OpenAI posterior replicas)
-- statement:
--   **Learners.** A `Learner d M T Ω` is a sequential learner with $2^M$ memory states whose randomness is a seed $\omega \in \Omega$ fixed in advance. Given $\omega$ it is deterministic: an initial (stop flag, state); at time $t$, in state $a$, it maps an observation $(x, y) \in \mathbb R^d \times \mathbb R$ to a new (stop flag, state); and at each (time, state) it outputs a unit vector. Run on a signal $s$ and samples $x_0, \dots, x_{T-1}$, it reads the exact observations $(x_i, \langle x_i, s\rangle)$ one at a time until it stops or the samples run out, and outputs the estimate $\hat s$ attached to the terminal (time, state). `uniformSuccess ρ ε` is the probability that $\arccos\langle \hat s, s\rangle \le \varepsilon$ when $s$ is uniform on the unit sphere, the seed has law $\rho$, and the samples are independent standard Gaussian vectors.
--
--   `UniformAdmissible ρ` is a weaker measurability condition than `Admissible`: for $\rho$-almost every seed, every time and every state, the new-state part of the transition is almost everywhere measurable in the observation (for standard Gaussian times Lebesgue), and the estimate is almost everywhere measurable jointly in a uniform signal, the seed and the samples.
--
--   **The statement.** Let $A > 0$, $d \ge 32$, $M \le A d^2$, $0 < \varepsilon \le 1/10$, let $\rho$ be a probability measure on $\Omega$, and let $L$ be a `UniformAdmissible` learner with $2^M$ states and horizon $T$ whose success probability is at least $2/3$. Then
--   $$\frac{1}{4(400000 + 100A)}\; d \log(1/\varepsilon) \;\le\; T.$$
--
--   Lean: `OAI.PosteriorRegression.source_fixed_quadratic_memory`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Learners/LearnerModelBridge.lean`). `Learner`, `UniformAdmissible` and `uniformSuccess` come from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Learners/LearnerModelBridge.lean (declaration OAI.PosteriorRegression.source_fixed_quadratic_memory)

import Mathlib
import Definitions.Def_OAIQWPR000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression

lemma source_fixed_quadratic_memory {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {A : ℝ} (hA : 0 < A) (hd : 32 ≤ d) (hM : (M:ℝ) ≤ A*(d:ℝ)^2)
    {ε : ℝ} (hε : 0<ε) (hε10 : ε≤1/10)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (L : Learner d M T Ω)
    (hL : L.UniformAdmissible ρ) (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (1 / (4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  sorry

end PosteriorRegression
end

end OAI
end
