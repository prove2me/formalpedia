-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_activeHull_exp_surjective
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.activeHull_exp_surjective
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-19T02:58:03.611544+00:00
-- url     : https://prove2.me/theorems/cd9b1ff5-0018-4960-a12d-258f2c06fecf
-- title:
--   Every point is reached from the active hull of a finite potential (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, with the Riemannian distance $d$. $\exp_x$ is the exponential map, and $c(x, y) = d(x, y)^2/2$ (`cost`). The **minimizing domain** of $x$ is $G_x = \{w \in T_xM : d(x, \exp_x w) = \|w\|\}$ (`minimizingDomain`). Fix a finite nonempty index set $\iota$, points $y : \iota \to M$ and numbers $h : \iota \to \mathbb R$. The **finite potential** is
--   $$u(x) = \max_{i \in \iota}\bigl(h_i - c(x, y_i)\bigr)$$
--   (`finitePotential`). The **active velocities** at $x$ are the minimizing velocities $a \in G_x$ with $\exp_x a = y_i$ for some index $i$ attaining the maximum (`activeVelocities`). The **active hull** at $x$ is their convex hull (`activeHull`).
--
--   **Statement.** For every $s > 0$ and every $z \in M$ there are $x \in M$ and $b$ in the active hull at $x$ with
--   $$\exp_x(s\,b) = z .$$
--
--   In the paper's language, the active hull at $x$ is the subdifferential of the potential, and the map $(x, b) \mapsto \exp_x(sb)$ on the active hull graph is the projection $F_s$. This statement is the surjectivity of $F_s$ for a finite potential, the paper's Lemma 4.5 ("Capture of every minimizing velocity"). Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.activeHull_exp_surjective`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Geodesics/MinimizerCapture.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Geodesics/MinimizerCapture.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.activeHull_exp_surjective)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem activeHull_exp_surjective (y : ι → M) (h : ι → ℝ)
    {s : ℝ} (hs : 0 < s) (z : M) :
    ∃ x : M, ∃ b ∈ activeHull (n := n) y h x, exp x (s•b) = z := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
