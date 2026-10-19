-- Prove2me | Theorems.Thm_OAI_ContinuumTemperature_exists_constructionData
-- name    : OAI.ContinuumTemperature.exists_constructionData
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:05:38.477811+00:00
-- url     : https://prove2.me/theorems/812e9290-d170-4b2a-83dc-d8ecbdf94029
-- title:
--   OpenAI's construction data for the continuum transition exist at the packing density (OpenAI continuum temperature)
-- statement:
--   **Statement.** There is a term of type `ConstructionData p`, where $p$ is `packingDensity` (the supremum over $L \ge 0$ of `packingNumber L` $/(L+2)^3$).
--
--   `ConstructionData p` is OpenAI's structure recording the data of their construction of the pair potential. It consists of:
--   - real numbers $t, \tau, \gamma$ with $0 < \tau \le p/100$ and $\gamma > 0$, and `ConstructionCap t (firstMass p + 1)`, where `firstMass p` $= 3/(2p)$ and `ConstructionCap t M` says $1 < t$, $0 < M$, $140608 \cdot$ `kernelHeight` $\cdot M \le t$ and $1024\,M < t$;
--   - a geometric condition: for every three points $w_0, w_1, w_2$ of $\mathbb R \times \mathbb R$ with each $w_i$ within distance $\tau$ of `triangleVertex p i` (the points $(0,0)$, $(3p/4, p)$, $(12p, 4p)$), the closed ball of radius $\gamma$ about `triangleCenter p` $= (17p/4, 5p/3)$ lies in the convex hull of $\{w_0, w_1, w_2\}$;
--   - a sequence of stages `stages n : ConstructionStage t p τ n` and a sequence `ranges : ℕ → ℝ`, where stage $0$ has the zero mass sequence and leading mass `firstMass p`, and each pair of consecutive stages satisfies `StageTransition (stages n) (stages (n+1)) (ranges n)`.
--
--   A stage carries a mass sequence $\sigma$, a range sequence $R$, a leading mass $a$ and a point $x$, with the constraints of `ConstructionStage` (nonnegative summable masses, ranges at least $1$, a mass budget, $x$ close to `initialPoint`, and a vertex-triple condition on the mean-field transform of the stage's physical pressure). A transition prepends the leading mass and a new range greater than $4$ to the sequences and controls the next leading mass, the displacement of $x$ and the change of the pressure on the closed ball of radius $1/4$ about `initialPoint` $= (1, -3/4)$, by explicit geometric budgets.
--
--   Lean: `OAI.ContinuumTemperature.exists_constructionData`, OpenAI's lemma of that name (in `lean/OAI/Probability/ContinuumTransition/ConstructionSequence.lean`). `ConstructionData`, `ConstructionStage`, `StageTransition`, `ConstructionCap`, `firstMass`, `kernelHeight`, `triangleVertex`, `triangleCenter`, `initialPoint`, `packingDensity` and `packingNumber` come from the definitions bundle `OAIQWCT000` of this split, where every field is stated in full.
-- source:
--   OpenAI, A continuum temperature singularity for a radial pair potential, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ContinuumTransition/ConstructionSequence.lean (declaration OAI.ContinuumTemperature.exists_constructionData)

import Mathlib
import Definitions.Def_OAIQWCT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma exists_constructionData : Nonempty (ConstructionData packingDensity) := by
  sorry

end ContinuumTemperature
end
end

end OAI
end
