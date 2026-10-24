-- Prove2me | Theorems.Thm_OAI_Bernoulli_DeSilvaJerison_U_upper_lipschitz_comparison
-- name    : OAI.Bernoulli.DeSilvaJerison.U_upper_lipschitz_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:35:52.597223+00:00
-- url     : https://prove2.me/theorems/4a22a56d-74e9-4b3b-a5c6-24f7e5c7a8b3
-- title:
--   Lipschitz competitors above the De Silva–Jerison cone U have no smaller Bernoulli energy (OpenAI Bernoulli cone)
-- statement:
--   **Notation** (definitions bundle `OAIQWBNS000` of this split). $U$ is the De Silva–Jerison cone on $\mathbb R^7$ (`DeSilvaJerison.U`): $U(x) = \kappa\,\lVert x\rVert\,p(x_7/\lVert x\rVert)$, with the explicit spherical profile $p$ = `DeSilvaJerison.p` and normalization $\kappa$ = `DeSilvaJerison.κ`; see the statement `OAI.Bernoulli.DeSilvaJerison.U_global_minimizer`. For a set $D$, a function $u$ and a vector field $G$, `energy D u G` is $\int_D \bigl(\lVert G\rVert^2 + \mathbf 1_{\{u > 0\}}\bigr)$, and `gradient` is the Fréchet gradient.
--
--   **The statement.** Let $v : \mathbb R^7 \to \mathbb R$ be Lipschitz with $U \le v$ everywhere, such that $v - U$ has compact support. Let $c \in \mathbb R^7$ and $r \in \mathbb R$ be such that the closed support of $v - U$ lies in the open ball $B = B(c, r)$. Then
--   $$\int_B \Bigl(\lVert \nabla U\rVert^2 + \mathbf 1_{\{U > 0\}}\Bigr) \;\le\; \int_B \Bigl(\lVert \nabla v\rVert^2 + \mathbf 1_{\{v > 0\}}\Bigr),$$
--   with $\nabla$ the pointwise gradient (`gradient U`, `gradient v`), which exists almost everywhere for Lipschitz functions.
--
--   This is the upper half of the comparison in De Silva and Jerison's minimality proof for $U$: competitors lying above $U$ are handled by a calibration built from a foliation of the region above $U$ by dilates of a supersolution. The global minimality of $U$ then combines it with the comparison for competitors below $U$.
--
--   Lean: `OAI.Bernoulli.DeSilvaJerison.U_upper_lipschitz_comparison`, OpenAI's theorem of that name (in `lean/OAI/Analysis/BernoulliCone/UpperLipschitzComparison.lean`).
-- source:
--   OpenAI, The critical dimension for one-phase Bernoulli minimizers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 367; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BernoulliCone/UpperLipschitzComparison.lean (declaration OAI.Bernoulli.DeSilvaJerison.U_upper_lipschitz_comparison)

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
open Foliation

theorem U_upper_lipschitz_comparison {v:Space 7→ℝ} {L:ℝ≥0}
    (hv:LipschitzWith L v) (hUv:∀x,U x≤v x)
    (hc:HasCompactSupport (fun y=>v y-U y))
    {c:Space 7} {r:ℝ} (hS:tsupport (fun y=>v y-U y)⊆Metric.ball c r) :
    energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r) v (gradient v) := by
  sorry
end Bernoulli.DeSilvaJerison

end
end

end OAI
end
