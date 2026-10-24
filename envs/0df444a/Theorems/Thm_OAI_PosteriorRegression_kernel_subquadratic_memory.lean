-- Prove2me | Theorems.Thm_OAI_PosteriorRegression_kernel_subquadratic_memory
-- name    : OAI.PosteriorRegression.kernel_subquadratic_memory
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:30:59.481218+00:00
-- url     : https://prove2.me/theorems/5a62f07b-7b08-4344-9c67-1eb474df0098
-- title:
--   Learners with o(d²) bits of memory need Ω(d log(1/ε)) exact Gaussian measurements (OpenAI posterior replicas, Theorem 1.2)
-- statement:
--   **Learners.** A `CompletedKernelLearner d M` is a randomized sequential learner with $2^M$ memory states. It has an initial law on pairs (stop flag, state); at each time $t$ and state $a$, a Markov kernel takes an observation $(x, y) \in \mathbb R^d \times \mathbb R$ to a new pair (stop flag, state), where observations carry the completion of the Borel σ-algebra for (standard Gaussian) × (Lebesgue); and at each (time, state) an output law on the unit sphere. Run on a signal $s$ and samples $x_0, \dots, x_{T-1}$, it reads the exact observations $(x_i, \langle x_i, s\rangle)$ one at a time until it stops or the samples run out, then draws its estimate $\hat s$ from the output law at the terminal (time, state) (`estimateLaw`). A `JointKernelExperiment d M T Ω ρ` is a family of such learners `rules ω` indexed by a seed $\omega$ drawn from $\rho$, together with a jointly measurable output kernel that agrees almost everywhere with each learner's estimate law. `uniformSuccess ε` is the probability that $\arccos\langle \hat s, s\rangle \le \varepsilon$ when the seed has law $\rho$, the signal $s$ is uniform on the unit sphere, and the samples are independent standard Gaussian vectors.
--
--   **The statement.** There is a constant $c > 0$ with the following property. Let $M : \mathbb N \to \mathbb N$ satisfy $M(d) = o(d^2)$. Then there is a $d_0$ such that for every $d \ge d_0$, every $T$, every $\varepsilon$ with $0 < \varepsilon \le 1/10$, every probability space $(\Omega, \rho)$ and every joint kernel experiment with $2^{M(d)}$ states and horizon $T$ whose success probability is at least $2/3$,
--   $$c\, d \log(1/\varepsilon) \;\le\; T.$$
--
--   This is the proposition `PosteriorRegression.KernelSubquadraticMemory` of the published bundle `Def_PosteriorReplicas`, the eighth component of the goal `OAI.PosteriorReplicas.source_main`; it is the Lean form of the paper's Theorem 1.2 (uniform-prior sample lower bound).
--
--   Lean: `OAI.PosteriorRegression.kernel_subquadratic_memory`, OpenAI's theorem of that name (in `lean/OAI/Probability/PosteriorReplicas/Learners/JointKernelExperiment.lean`).
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, Theorem 1.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Learners/JointKernelExperiment.lean (declaration OAI.PosteriorRegression.kernel_subquadratic_memory)

import Mathlib
import Definitions.Def_PosteriorReplicas

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression

theorem kernel_subquadratic_memory : KernelSubquadraticMemory.{u} := by
  sorry

end PosteriorRegression
end

end OAI
end
