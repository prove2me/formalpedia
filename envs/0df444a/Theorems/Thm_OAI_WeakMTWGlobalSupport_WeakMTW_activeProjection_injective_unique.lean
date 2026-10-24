-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_activeProjection_injective_unique
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.activeProjection_injective_unique
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:58:44.372352+00:00
-- url     : https://prove2.me/theorems/c860abfa-f2a3-40fb-bc71-d255a0af1bcc
-- title:
--   An injective projection makes the scaled active velocity the unique minimizing velocity (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, with the Riemannian distance $d$, the exponential map $\exp$ and the cost $c = d^2/2$. The minimizing domain of $x$ is $G_x = \{w \in T_xM : d(x, \exp_x w) = \|w\|\}$ (`minimizingDomain`). Fix a finite nonempty index set $\iota$, points $y_i$ and numbers $h_i$. The finite potential is $u = \max_i (h_i - c(\cdot, y_i))$. The active hull at $x$ is the convex hull of the minimizing velocities from $x$ to the active points $y_i$ (`activeHull`). The active hull graph $\Gamma$ is the set of pairs $(x, b)$ with $b$ in the active hull at $x$, and $F_s(x, b) = \exp_x(s b)$ on $\Gamma$ (`activeProjection`).
--
--   **Statement.** Let $s > 0$, and suppose $F_s : \Gamma \to M$ is injective. Let $b$ be in the active hull at $x$, and let $w \in G_x$ be a minimizing velocity with $\exp_x w = \exp_x(s b)$. Then
--   $$w = s\,b .$$
--
--   So once the projection at scale $s$ is injective, $s b$ is the only minimizing velocity from $x$ to $\exp_x(s b)$. This is the uniqueness step in the paper's proof of Theorem 4.8: "Injectivity forces $x' = x$ and $w = t_* p$". Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.activeProjection_injective_unique`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/ActiveContinuation.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/ActiveContinuation.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.activeProjection_injective_unique)

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

 theorem activeProjection_injective_unique (y : ι → M) (h : ι → ℝ)
     {s : ℝ} (hs : 0 < s) (hinj : Function.Injective (activeProjection (n := n) y h s))
     {x : M} {b : TangentSpace (model n) x} (hb : b ∈ activeHull y h x)
     {w : TangentSpace (model n) x} (hw : w ∈ minimizingDomain x)
     (he : exp x w = exp x (s•b)) : w = s•b := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
