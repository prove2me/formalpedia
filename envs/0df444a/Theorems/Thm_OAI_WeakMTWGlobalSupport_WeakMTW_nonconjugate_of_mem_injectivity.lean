-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_nonconjugate_of_mem_injectivity
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_of_mem_injectivity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T03:00:46.83604+00:00
-- url     : https://prove2.me/theorems/99d00a65-46c1-4bc8-8f5a-b9a66b0dee52
-- title:
--   Velocities of the injectivity domain are nonconjugate (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth manifold modelled on $\mathbb R^n$ (`Model n`) with a smooth Riemannian metric, whose metric-space distance is the Riemannian distance (Mathlib's `IsRiemannianManifold`). `exp x w` is the exponential map at $x$. The **injectivity domain** `injectivityDomain x` is the set of $v \in T_xM$ whose geodesic $t \mapsto \exp_x(tv)$ is still minimizing a little beyond time $1$: some $a > 1$ has $d(x, \exp_x(av)) = a\|v\|$. A velocity $v$ is **nonconjugate** (`Nonconjugate x v`, from the definitions bundle `OAIQWMTW002`) if the derivative at $v$ of $w \mapsto \varphi(\exp_x w)$ is injective, where $\varphi$ is the preferred chart at $\exp_x v$.
--
--   **Statement.** For every $x \in M$ and every $v$ in the injectivity domain of $x$, the velocity $v$ is nonconjugate.
--
--   This is the nonconjugacy half of the paper's Lemma 2.1 (interior characterization): a velocity of the interior injectivity domain is nonconjugate. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_of_mem_injectivity`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Geodesics/NonconjugateBranches.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Geodesics/NonconjugateBranches.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.nonconjugate_of_mem_injectivity)

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

 theorem nonconjugate_of_mem_injectivity (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) : Nonconjugate x v := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
