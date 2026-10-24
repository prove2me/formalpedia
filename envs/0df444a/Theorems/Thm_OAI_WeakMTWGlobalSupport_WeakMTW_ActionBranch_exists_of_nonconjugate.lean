-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_ActionBranch_exists_of_nonconjugate
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.exists_of_nonconjugate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:46:23.818986+00:00
-- url     : https://prove2.me/theorems/4996012c-283b-456d-a008-4f5786fa0660
-- title:
--   A smooth inverse branch of the exponential pair map at every nonconjugate velocity (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$ (`Model n`), whose distance is the Riemannian distance, with exponential map `exp`. For $x \in M$, `stateChart x` is the chart of the tangent bundle $TM$ at $(x, 0)$, with values in $\mathbb R^n \times \mathbb R^n$. For $x, y \in M$, `pairExpCoordinates x y` is the map $\Psi(z, u) = (z, \exp_z u)$ read in charts: a point $(a, u)$ in the image of `stateChart x` goes to $a$ and the chart-at-$y$ coordinates of the time-1 point of the geodesic with that initial state. Its natural domain `pairExpDomain x y` is the set where this makes sense. An **action branch** `ActionBranch x y` is a local inverse of this map: an open partial homeomorphism $e$ of $\mathbb R^n \times \mathbb R^n$ that agrees with `pairExpCoordinates x y` as a function, has its source inside `pairExpDomain x y`, and has a $C^\infty$ inverse on its target. A velocity $v \in T_xM$ is **nonconjugate** (`Nonconjugate x v`) if the derivative at $v$ of $w \mapsto \exp_x w$, read in the chart at $\exp_x v$, is injective.
--
--   **Statement.** If $v \in T_xM$ is nonconjugate, there is an action branch $B$ from $x$ to $\exp_x v$ whose source contains the tangent-bundle coordinates of $(x, v)$.
--
--   This is the first step of the paper's Section 2.1 ("Smooth geodesic branches"): at a nonconjugate velocity, the map $\Psi$ of the paper's equation (2.3) has a smooth local inverse, which defines the branch cost. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.exists_of_nonconjugate`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/ActionBranch.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/ActionBranch.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.ActionBranch.exists_of_nonconjugate)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003

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
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 namespace ActionBranch
 variable {x y : M}

 theorem exists_of_nonconjugate {v : TangentSpace (model n) x} (hn : Nonconjugate x v) :
    ∃ B : ActionBranch (n := n) x (exp x v),
      stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source := by
  sorry

 end ActionBranch
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
