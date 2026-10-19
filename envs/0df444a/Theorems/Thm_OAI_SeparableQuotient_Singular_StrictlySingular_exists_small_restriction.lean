-- Prove2me | Theorems.Thm_OAI_SeparableQuotient_Singular_StrictlySingular_exists_small_restriction
-- name    : OAI.SeparableQuotient.Singular.StrictlySingular.exists_small_restriction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T20:47:01.277433+00:00
-- url     : https://prove2.me/theorems/1fb719a4-f374-4fea-a3d3-b02265409648
-- title:
--   A strictly singular operator has arbitrarily small norm on some closed infinite-dimensional subspace of any closed infinite-dimensional subspace (Kato)
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ (`𝕜 : Type*` with `[RCLike 𝕜]`), and let $Y$ and $Z$ be normed spaces over $\mathbb{K}$ (`[NormedAddCommGroup Y] [NormedSpace 𝕜 Y]`, and likewise for $Z$). Completeness is not assumed. Let $T : Y \to Z$ be a bounded linear operator (`T : Y →L[𝕜] Z`) that is strictly singular in the following sense (`hT`): for every closed infinite-dimensional subspace $M' \le Y$ (`M' : Submodule 𝕜 Y`, `IsClosed (M' : Set Y)`, `¬ FiniteDimensional 𝕜 M'`) and every $c > 0$ there is $x \in M'$ with $\|Tx\| < c\,\|x\|$. In words, $T$ is not bounded below on any closed infinite-dimensional subspace.
--
--   Let $M \le Y$ be a closed infinite-dimensional subspace (`hM`, `hI`) and let $\varepsilon > 0$ (`hε`). Then there is a subspace $N \le M$ that is closed and infinite-dimensional, with
--   $$\|Tx\| \le \varepsilon\,\|x\| \qquad \text{for every } x \in N .$$
--
--   This is the lemma of Kato (1958) that a strictly singular operator has arbitrarily small norm on a suitable closed infinite-dimensional subspace of any given one.
--
--   Lean: `OAI.SeparableQuotient.Singular.StrictlySingular.exists_small_restriction`, OpenAI's theorem of that name in `lean/OAI/Analysis/SeparableQuotients/StrictSingularity.lean`. OpenAI states the hypothesis as `StrictlySingular T`, a one-line definition equal to the hypothesis `hT` above. This statement writes the definition out, so it needs only Mathlib. Otherwise the hypotheses and conclusion are OpenAI's.
-- source:
--   T. Kato, Perturbation theory for nullity, deficiency and other quantities of linear operators, J. Analyse Math. 6 (1958), 261–322 (strictly singular operators and this lemma). Lean proof: OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SeparableQuotients/StrictSingularity.lean (declaration OAI.SeparableQuotient.Singular.StrictlySingular.exists_small_restriction)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem StrictlySingular.exists_small_restriction (T : Y →L[𝕜] Z)
    (hT : ∀ M : Submodule 𝕜 Y, IsClosed (M : Set Y) → ¬ FiniteDimensional 𝕜 M →
      ∀ c : ℝ, 0 < c → ∃ x : M, ‖T x‖ < c*‖x‖)
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : Submodule 𝕜 Y, N ≤ M ∧ IsClosed (N : Set Y) ∧ ¬ FiniteDimensional 𝕜 N ∧
      ∀ x ∈ N, ‖T x‖ ≤ ε*‖x‖ := by
  sorry

end SeparableQuotient.Singular

end

end OAI
end
