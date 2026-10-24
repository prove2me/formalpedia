-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_critical_jensen
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.critical_jensen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:48:13.18362+00:00
-- url     : https://prove2.me/theorems/b10ec2f7-eae9-414d-a3cf-def3dba2580a
-- title:
--   Transverse Jensen inequality for the cost Hessian up to a first cut (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact Riemannian manifold modelled on $\mathbb R^n$, with exponential map `exp`, cost $c(x, y) = d(x, y)^2/2$, and **injectivity domain** $I(x)$ (`injectivityDomain x`), the velocities $v \in T_xM$ whose geodesic $\tau \mapsto \exp_x(\tau v)$ is still minimizing slightly beyond $\tau = 1$. Weak MTW (`HasWeakMTW`) says that the Ma–Trudinger–Wang form `mtw x v ξ η` is nonnegative for all $v \in I(x)$ and all orthogonal $\xi, \eta$. From the bundles of this split:
--   - $A_x(v)$ (`actionHessian x v`) is the covariant Hessian at $x$ of the cost $c(\cdot, \exp_x v)$, computed in the chart at $x$, as a bilinear form on $T_xM$;
--   - an **action branch** $B$ from $x$ to $z$ (`ActionBranch x z`) is a smooth local inverse, in charts, of the pair exponential map $(x', w) \mapsto (x', \exp_{x'} w)$ near $x$ and $z$ (`pairExpCoordinates`). Its value `B.value` is the branch cost, half the squared length of the inverse-branch velocity;
--   - `branchHessianDiag x z B.coord v ξ` is the covariant Hessian of that branch cost at $(x, \exp_x v)$ in the direction $\xi$: its second chart derivative plus the Christoffel correction.
--
--   **Statement.** Assume weak MTW. Let $x \in M$, $\xi \in T_xM$, $S \subseteq T_xM$ convex and $s > 0$, with $rS \subseteq I(x)$ for all $0 \le r < s$. Let $a_i \in S$ ($i$ in a finite type), with weights $\theta_i \ge 0$, $\sum_i \theta_i = 1$, and barycenter $b = \sum_i \theta_i a_i \in S$. Suppose $\langle \xi, a_i - b\rangle = 0$ whenever $\theta_i \neq 0$, and $s a_i \in I(x)$ for all $i$. Let $B$ be an action branch from $x$ to $\exp_x(sb)$ whose coordinate source contains the state $(x, sb)$. Then
--   $$\sum_i \theta_i\, A_x(s a_i)(\xi, \xi) \;\le\; \texttt{branchHessianDiag}\bigl(x, \exp_x(sb), B, sb, \xi\bigr).$$
--
--   This is the finite Jensen inequality of the paper's Lemma 2.4 ("Transverse concavity"), at the first scale $s$, where $sb$ itself may be a cut velocity. The right side is the Hessian of the smooth branch through $sb$, the limit of $A_x(rb)$ as $r \uparrow s$. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.critical_jensen`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/CriticalJensen.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/CriticalJensen.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.critical_jensen)

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
open scoped Topology ContDiff Manifold Pointwise
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem critical_jensen (hMTW : HasWeakMTW (n := n) (M := M)) (x : M)
    (ξ : TangentSpace (model n) x) {S : Set (TangentSpace (model n) x)}
    (hS : Convex ℝ S) {s : ℝ} (hs : 0 < s)
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ S, r•a ∈ injectivityDomain x)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b : TangentSpace (model n) x} (hb : b ∈ S) (ha : ∀ i, a i ∈ S)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1) (hbary : ∑ i, θ i • a i = b)
    (horth : ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0)
    (haI : ∀ i, s•a i ∈ injectivityDomain x)
    (B : ActionBranch (n := n) x (exp x (s•b)))
    (hB : stateChart x (⟨x,s•b⟩ : TangentBundle (model n) M) ∈ B.coord.source) :
    (∑ i, θ i * actionHessian x (s•a i) ξ ξ) ≤
      branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
