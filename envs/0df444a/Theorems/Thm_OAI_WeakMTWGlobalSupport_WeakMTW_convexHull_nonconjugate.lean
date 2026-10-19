-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_convexHull_nonconjugate
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.convexHull_nonconjugate
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-19T03:00:52.727889+00:00
-- url     : https://prove2.me/theorems/0d1ca8bb-a165-4c3d-84f5-db5969518885
-- title:
--   Under weak MTW a minimizing convex hull of nonconjugate velocities is nonconjugate (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, with the Riemannian distance $d$, the exponential map $\exp$, the cost $c = d^2/2$ and the injectivity domains $I(x)$ (`injectivityDomain`). The **weak MTW condition** (`HasWeakMTW`) says $\mathfrak S_{(x,v)}(\xi, \eta) \ge 0$ for all $x$, all $v \in I(x)$ and all orthogonal $\xi, \eta \in T_xM$. Here $\mathfrak S_{(x,v)}(\xi,\eta)$ (`mtw`) is $-\tfrac32$ times the mixed fourth derivative $\partial_s^2\partial_t^2$ at $0$ of $c(\exp_x(t\xi), \exp_x(v + s\eta))$. The minimizing domain is $G_x = \{w : d(x, \exp_x w) = \|w\|\}$ (`minimizingDomain`). A velocity $v \in T_xM$ is **nonconjugate** (`Nonconjugate`) if the differential at $v$ of $\exp_x$, read in a chart at $\exp_x v$, is injective.
--
--   **Statement.** Assume weak MTW. Let $x \in M$ and let $A \subseteq T_xM$ be a set of nonconjugate velocities whose convex hull lies in $G_x$. Then every velocity in the convex hull of $A$ is nonconjugate.
--
--   This is the paper's Corollary 3.2 ("Nonconjugacy of a minimizing convex hull"). Here $A$ may be any set, not only a finite one. It follows from the paper's Proposition 3.1 for segments. The argument applies weak MTW at proper radial contractions, where the cost is smooth. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.convexHull_nonconjugate`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/HullNonconjugacy.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/HullNonconjugacy.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.convexHull_nonconjugate)

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
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem convexHull_nonconjugate (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) {A : Set (TangentSpace (model n) x)}
    (hA : ∀ a ∈ A, Nonconjugate x a)
    (hmin : convexHull ℝ A ⊆ minimizingDomain x) :
    ∀ v ∈ convexHull ℝ A, Nonconjugate x v := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
