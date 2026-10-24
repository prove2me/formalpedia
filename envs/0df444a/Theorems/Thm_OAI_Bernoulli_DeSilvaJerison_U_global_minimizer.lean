-- Prove2me | Theorems.Thm_OAI_Bernoulli_DeSilvaJerison_U_global_minimizer
-- name    : OAI.Bernoulli.DeSilvaJerison.U_global_minimizer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:35:58.653906+00:00
-- url     : https://prove2.me/theorems/df4bd82d-2c4a-42a1-8b5d-f1e753ae2b64
-- title:
--   De Silva–Jerison theorem: the double cone U in ℝ⁷ is a global minimizer of the one-phase Bernoulli energy (OpenAI Bernoulli cone)
-- statement:
--   **The cone** (definitions bundle `OAIQWBNS000` of this split). Write $x = (x_1, \dots, x_7) \in \mathbb R^7$ (`Space 7`). An explicit even profile $f$ on $(-1, 1)$ has a first positive root $t_7 \approx 0.51733$ (`DeSilvaJerison.t7`). Put $p(t) = f(\min(|t|, t_7))$ (`DeSilvaJerison.p`), which is positive for $|t| < t_7$ and zero otherwise, and $c_7 = (1 - t_7^2)\,f'(t_7)^2$. The De Silva–Jerison cone is
--   $$U(x) \;=\; c_7^{-1/2}\,\lVert x\rVert\; p\!\left(\frac{x_7}{\lVert x\rVert}\right)$$
--   (`DeSilvaJerison.U`, with $\kappa = c_7^{-1/2}$ = `DeSilvaJerison.κ`). It is nonnegative, one-homogeneous and axially symmetric, and it is positive exactly on the double cone $|x_7| < t_7 \lVert x\rVert$.
--
--   **The statement.** $U$ is a global minimizer of the one-phase Bernoulli energy in the sense of the published bundle `Def_BernoulliNonflatInSeven` (`GlobalMinimizer U`). That is, $U \ge 0$ almost everywhere, and $U$ has a weak gradient $G$ that is in $H^1$ on every ball. For every open ball $B$ of positive radius and every competitor $v \in H^1(B)$ with weak gradient $V$, $v \ge 0$ almost everywhere on $B$ and $(v - U, V - G) \in H^1_0(B)$, the energies satisfy
--   $$\int_B \Bigl(\lVert G\rVert^2 + \mathbf 1_{\{U > 0\}}\Bigr) \;\le\; \int_B \Bigl(\lVert V\rVert^2 + \mathbf 1_{\{v > 0\}}\Bigr).$$
--
--   This is De Silva and Jerison's Theorem 1.1 (J. Reine Angew. Math. 635, 2009), which the paper cites for the dimension-seven half of its Theorem 1.1. OpenAI's Lean development proves it in full.
--
--   Lean: `OAI.Bernoulli.DeSilvaJerison.U_global_minimizer`, OpenAI's theorem of that name (in `lean/OAI/Analysis/BernoulliCone/GlobalMinimizer.lean`).
-- source:
--   OpenAI, The critical dimension for one-phase Bernoulli minimizers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 367; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf; Apache License 2.0), citing D. De Silva and D. Jerison, A singular energy minimizing free boundary, J. Reine Angew. Math. 635 (2009), 1–21, Theorem 1.1, https://doi.org/10.1515/CRELLE.2009.074; Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BernoulliCone/GlobalMinimizer.lean (declaration OAI.Bernoulli.DeSilvaJerison.U_global_minimizer)

import Mathlib
import Definitions.Def_BernoulliNonflatInSeven
import Definitions.Def_OAIQWBNS000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison

theorem U_global_minimizer : GlobalMinimizer U := by
  sorry

end Bernoulli.DeSilvaJerison

end
end

end OAI
end
