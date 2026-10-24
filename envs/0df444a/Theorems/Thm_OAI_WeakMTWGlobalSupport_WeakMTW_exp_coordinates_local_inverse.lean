-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exp_coordinates_local_inverse
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.exp_coordinates_local_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:57:10.308261+00:00
-- url     : https://prove2.me/theorems/fd4e1d7e-7805-4129-8e1b-fafbd3973455
-- title:
--   The exponential map is a local diffeomorphism at every velocity of the injectivity domain (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth manifold modelled on $\mathbb R^n$ (`Model n`) with a smooth Riemannian metric, whose metric-space distance is the Riemannian distance (Mathlib's `IsRiemannianManifold`). `exp b w` is the exponential map at $b$. The **injectivity domain** `injectivityDomain b` is the set of $v \in T_bM$ whose geodesic $t \mapsto \exp_b(tv)$ is still minimizing a little beyond time $1$: some $a > 1$ has $d(b, \exp_b(av)) = a\|v\|$. For a point $x$, `chartAt (Model n) x` is the preferred chart of $M$ at $x$.
--
--   **Statement.** Let $b, x \in M$ and $v \in T_bM$ in the injectivity domain of $b$, with $\exp_b v$ in the source of the chart at $x$. Then there is a partial homeomorphism $e$ from $T_bM$ to $\mathbb R^n$ such that
--   - $e(w) = \varphi_x(\exp_b w)$ for every $w$, where $\varphi_x$ is the chart at $x$;
--   - $v$ lies in the source of $e$, and $\exp_b w$ lies in the source of $\varphi_x$ for every $w$ in the source of $e$;
--   - the inverse $e^{-1}$ is $C^\infty$ on the target of $e$.
--
--   So $\exp_b$, read in a chart, is a local diffeomorphism near every velocity of the injectivity domain. These velocities are nonconjugate. This is part of the paper's Lemma 2.1 (interior characterization): a velocity of the interior injectivity domain is nonconjugate, so the exponential map has invertible differential there. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.exp_coordinates_local_inverse`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Geodesics/FibreNonfocal.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport`.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Geodesics/FibreNonfocal.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.exp_coordinates_local_inverse)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport

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

 theorem exp_coordinates_local_inverse (b x : M) {v : TangentSpace (model n) b}
    (hv : v ∈ injectivityDomain b) (hx : exp b v ∈ (chartAt (Model n) x).source) :
    ∃ e : OpenPartialHomeomorph (TangentSpace (model n) b) (Model n),
      (∀ w, e w = chartAt (Model n) x (exp b w)) ∧ v ∈ e.source ∧
      (∀ w ∈ e.source, exp b w ∈ (chartAt (Model n) x).source) ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
