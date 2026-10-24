-- Prove2me | Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_basePotential_chart_control
-- name    : OAI.PinchedHartogs.BaseConstruction.basePotential_chart_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:05:45.001993+00:00
-- url     : https://prove2.me/theorems/4574f7e9-579d-4c66-a3a7-aa1acfb7d13d
-- title:
--   Chart control of the base potential (OpenAI pinched Kähler threefold, Lemma 6.3)
-- statement:
--   `ChartControl φ c C` and `ChartJets φ C` (the chart bounds (2.2) and (2.3) of the paper on the complex Hessian of $\varphi$ in the centered automorphism charts of the unit ball of $\mathbb C^2$) are from the published bundle `Def_PinchedKahler`; see the published statement `OAI.PinchedHartogs.controlled_potential`. From the definitions bundle `OAIQWPH001` of this split: `Sphere`, `ProjectivelySeparated` and `logarithmicTest` (see the published statement `OAI.PinchedHartogs.BaseConstruction.testSeries_chart_uniform_jets`), and the base potential
--   $$\mathrm{basePotential}\,P\,a\,\varepsilon\,L\,Q\,(z) \;=\; \psi(z) + L\sum_{j\ge 0}\mathrm{logarithmicTest}(a, \varepsilon, P(Q^{j+1}), Q^{j+1})(z), \qquad \psi(z) = -\log(1-|z|^2)$$
--   (the paper's (6.1)).
--
--   **Statement.** Let $a \in \mathbb R$, $\varepsilon \ne 0$, $D \ge 1$, $L \ge 0$, $Q \ge 2$, and let the finite sets $P(Q^{j+1})$ be `ProjectivelySeparated` at scale $D/\sqrt{Q^{j+1}}$. Then there is $C$ with `ChartControl (basePotential P a ε L Q) 1 C` and `ChartJets (basePotential P a ε L Q) C`.
--
--   This is Lemma 6.3 of the paper: the base potential satisfies the chart bounds (2.2) and (2.3) with $c = 1$.
--
--   Lean: `OAI.PinchedHartogs.BaseConstruction.basePotential_chart_control`, OpenAI's theorem of that name (in `lean/OAI/Geometry/Kahler/BasePotentialControl.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf, Lemma 6.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Kahler/BasePotentialControl.lean (declaration OAI.PinchedHartogs.BaseConstruction.basePotential_chart_control)

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma basePotential_chart_control (a : ℝ) {ε D L : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D) (hL : 0 ≤ L)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) :
    ∃ C : ℝ, ChartControl (basePotential P a ε L Q) 1 C ∧ ChartJets (basePotential P a ε L Q) C := by
  sorry

end PinchedHartogs.BaseConstruction

end

end OAI
end
