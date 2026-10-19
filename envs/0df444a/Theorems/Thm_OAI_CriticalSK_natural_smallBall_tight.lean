-- Prove2me | Theorems.Thm_OAI_CriticalSK_natural_smallBall_tight
-- name    : OAI.CriticalSK.natural_smallBall_tight
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T21:37:07.331985+00:00
-- url     : https://prove2.me/theorems/6a31ec3c-7232-4e8e-9e32-81625bf3be1c
-- title:
--   Small-ball obstruction at scale n^{1/3} is unlikely under the SK disorder (OpenAI, critical SK slow mixing)
-- statement:
--   Let $\delta > 0$ and $\alpha > 0$ (`hδ`, `hα`). Then there is a $b > 0$ with the following property. For all large $n$, let $N = n + 4$. Draw the SK disorder $W$ on $N$ spins from `disorderLaw N`: independent centred Gaussian couplings $W_{ij}$ of variance $1/N$, one for each pair $i < j$. Consider the event that every unit direction is "small" with Gibbs mass at least $\delta$. Precisely, for every $a \in \mathbb{R}^N$ with $\|a\| = 1$, the Gibbs measure of $W$ gives mass at least $\delta$ to the spin configurations $x \in \{\pm1\}^N$ with $\bigl|\sum_i a_i x_i\bigr| \le b N^{1/3}$. This event has probability less than $\alpha$:
--   $$\mathbb{P}\bigl(W \in \texttt{smallBallObstruction}\ N\ (b N^{1/3})\ \delta\bigr) < \alpha .$$
--
--   `disorderLaw` and the Gibbs measure `gibbs` come from the published bundle `Def_CriticalSK`. `smallBallObstruction` and the Gibbs small-ball mass `linearSmallBall` come from the definitions bundle `OAIQWCSK000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.CriticalSK.natural_smallBall_tight`, OpenAI's lemma of that name in `lean/OAI/MathematicalPhysics/CriticalSK/SmallBall.lean`.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/SmallBall.lean (declaration OAI.CriticalSK.natural_smallBall_tight)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_OAIQWCSK000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real Filter

open scoped Topology

namespace CriticalSK

open Set MeasureTheory Filter

lemma natural_smallBall_tight {δ α : ℝ} (hδ : 0 < δ) (hα : 0 < α) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      (smallBallObstruction (n+4) (b*(n+4:ℝ)^(1/3:ℝ)) δ) < α := by
  sorry

end CriticalSK

end

end OAI
end
