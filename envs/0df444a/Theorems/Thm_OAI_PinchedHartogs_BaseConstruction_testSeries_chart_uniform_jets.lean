-- Prove2me | Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_testSeries_chart_uniform_jets
-- name    : OAI.PinchedHartogs.BaseConstruction.testSeries_chart_uniform_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:05:32.961847+00:00
-- url     : https://prove2.me/theorems/1fa0417c-1e4b-45bb-ad0d-6ce25b44ae2c
-- title:
--   Uniform chart jets of the logarithmic test series (OpenAI pinched Kähler threefold, Section 6)
-- statement:
--   `Base` ($\mathbb C^2$) and `centeredChart r U` (the automorphism-type chart of the unit ball centered at $U(r, 0)$) are from the published bundle `Def_PinchedKahler`. The other definitions are from the definitions bundle `OAIQWPH001` of this split: `Sphere` is the unit sphere of $\mathbb C^2$, `ProjectivelySeparated ρ P` says the points of $P$ are pairwise at projective distance at least $\rho$, and `logarithmicTest a ε P k z` is the regularized logarithmic test $\log\frac{|1 - a\,P_k(z)|^2 + \varepsilon^2}{1 + \varepsilon^2}$ of the peak polynomial $P_k(z) = \sum_{p \in P}\langle z, p\rangle^k$ (Section 5 of the paper).
--
--   **Statement.** Let $a \in \mathbb R$, $\varepsilon \ne 0$, $D \ge 1$, $Q \ge 2$, and let the finite sets $P(Q^{j+1}) \subseteq$ `Sphere` be `ProjectivelySeparated` at scale $D/\sqrt{Q^{j+1}}$. For every $n \ge 1$ there is $C \ge 0$ such that for all $0 \le r < 1$ and every unitary $U$ of $\mathbb C^2$, the $n$-th real derivative at $0$ of the test series in the chart satisfies
--   $$\Bigl\|D^n\Bigl(\sum_{j \ge 0} \mathrm{logarithmicTest}(a, \varepsilon, P(Q^{j+1}), Q^{j+1}) \circ \mathrm{centeredChart}(r, U)\Bigr)(0)\Bigr\| \le C.$$
--
--   This is the uniform chart estimate for the test series in Section 6 of the paper (Lemmas 6.1 and 6.3): the positive-order derivatives at the chart origins are bounded independently of the chart.
--
--   Lean: `OAI.PinchedHartogs.BaseConstruction.testSeries_chart_uniform_jets`, OpenAI's theorem of that name (in `lean/OAI/Geometry/Kahler/BaseChartUniform.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf, Lemmas 6.1 and 6.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Kahler/BaseChartUniform.lean (declaration OAI.PinchedHartogs.BaseConstruction.testSeries_chart_uniform_jets)

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

lemma testSeries_chart_uniform_jets (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base,
      ‖iteratedFDeriv ℝ n ((fun y => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) y) ∘ centeredChart r U) 0‖ ≤ C := by
  sorry

end PinchedHartogs.BaseConstruction

end

end OAI
end
