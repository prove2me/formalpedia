-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_branch_gradient_weighted
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.branch_gradient_weighted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:47:12.144466+00:00
-- url     : https://prove2.me/theorems/0873563f-676d-4039-bd72-e07f57c8d8d9
-- title:
--   Weighted cancellation of first-order terms of action branches (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact Riemannian manifold modelled on $\mathbb R^n$ (`Model n`), with exponential map `exp`. From the definitions bundle `OAIQWMTW003` of this split:
--   - `stateChart x` is the chart of the tangent bundle at $(x, 0)$;
--   - an **action branch** $B$ from $x$ to $z$ (`ActionBranch x z`) is a smooth local inverse, in the charts at $x$ and $z$, of the pair exponential map $(x', w) \mapsto (x', \exp_{x'} w)$ (`pairExpCoordinates`). Its value `B.value`, a function of the chart coordinates $(x', z')$ of the two endpoints, is the branch cost: half the squared length of the inverse-branch velocity.
--
--   **Statement.** Let $x, z, p \in M$ with $p$ in the chart domain at $x$. Let $a_i \in T_pM$ ($i$ in a finite type) and weights $\theta_i$ with $\sum_i \theta_i = 1$ and $\sum_i \theta_i a_i = b$; the weights need not be nonnegative. Let $s, \ell \in \mathbb R$ with $\ell \neq 0$. Let $B$ be an action branch from $x$ to $z$ whose coordinate source contains the chart state of $(p, sb)$. For each $i$, let $C_i$ be an action branch from $x$ to some point $z_i$ whose coordinate source contains the chart state of $(p, \ell a_i)$. Then for every $u \in \mathbb R^n$, writing $\partial_u$ for the derivative in the first endpoint in the direction $(u, 0)$,
--   $$\sum_i \theta_i\Bigl(\partial_u B.\mathrm{value}\bigl(p, \exp_p(sb)\bigr) - \tfrac{s}{\ell}\,\partial_u C_i.\mathrm{value}\bigl(p, \exp_p(\ell a_i)\bigr)\Bigr) = 0,$$
--   with points written in the charts at $x$, $z$ and $z_i$.
--
--   This is the exact cancellation of linear terms in the proof of the paper's Lemma 4.6 ("Local injectivity of the projection"): by first variation, the gradient of a branch cost in the first endpoint is minus the velocity, and the active representation $b = \sum_i \theta_i a_i$ makes the weighted gradients cancel (the paper's equation (4.9)). Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.branch_gradient_weighted`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/CollisionGradient.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/CollisionGradient.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.branch_gradient_weighted)

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

 theorem branch_gradient_weighted {x z p : M} {κ : Type*} [Fintype κ]
    (a : κ → TangentSpace (model n) p) (θ : κ → ℝ)
    {b : TangentSpace (model n) p} (hsum : ∑ i, θ i = 1)
    (hbary : ∑ i, θ i • a i = b) {s ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (hp : p ∈ (chartAt (Model n) x).source)
    (B : ActionBranch (n := n) x z)
    (hB : stateChart x (⟨p,s•b⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    (zC : κ → M) (C : ∀ i, ActionBranch (n := n) x (zC i))
    (hC : ∀ i, stateChart x (⟨p,ℓ•a i⟩ : TangentBundle (model n) M) ∈ (C i).coord.source)
    (u : Model n) :
    (∑ i, θ i*(fderiv ℝ B.value (chartAt (Model n) x p,chartAt (Model n) z (exp p (s•b))) (u,0) -
      (s/ℓ)*fderiv ℝ (C i).value
        (chartAt (Model n) x p,chartAt (Model n) (zC i) (exp p (ℓ•a i))) (u,0))) = 0 := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
