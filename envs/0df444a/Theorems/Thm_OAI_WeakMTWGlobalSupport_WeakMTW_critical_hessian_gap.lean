-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_critical_hessian_gap
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.critical_hessian_gap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:47:42.170905+00:00
-- url     : https://prove2.me/theorems/9616f6c0-28bc-402f-99c7-b7837d1541c6
-- title:
--   Strict transverse Hessian gap at a first cut scale (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statement `OAI.WeakMTWGlobalSupport.WeakMTW.critical_jensen` of this split. $M$ is a compact Riemannian manifold, with injectivity domain $I(x)$ and weak MTW condition `HasWeakMTW` from the published goal bundle. $A_x(v)$ (`actionHessian x v`) is the covariant Hessian at $x$ of the cost $c(\cdot, \exp_x v)$. For an action branch $B$ (`ActionBranch`), `branchHessianDiag` is the covariant Hessian of its branch cost. In addition, the **minimizing domain** $G_x$ (`minimizingDomain x`) is the set of $v$ with $d(x, \exp_x v) = \|v\|$.
--
--   **Statement.** Assume weak MTW. Let $x \in M$ and $\xi \in T_xM$, $\xi \neq 0$. Let $S \subseteq T_xM$ be convex, and let $0 < s < \ell < 1$ with $rS \subseteq I(x)$ for all $0 \le r < s$. Let $a_i \in S \cap G_x$ ($i$ in a finite type), with weights $\theta_i \ge 0$, $\sum_i \theta_i = 1$, and barycenter $b = \sum_i \theta_i a_i \in S$. Suppose $\langle \xi, a_i - b\rangle = 0$ whenever $\theta_i \neq 0$. Let $B$ be an action branch from $x$ to $\exp_x(sb)$ whose coordinate source contains the state $(x, sb)$. Then
--   $$0 \;<\; \sum_i \theta_i\Bigl(\texttt{branchHessianDiag}\bigl(x, \exp_x(sb), B, sb, \xi\bigr) - \tfrac{s}{\ell}\,A_x(\ell a_i)(\xi, \xi)\Bigr).$$
--
--   In the paper's notation $H_r(p) = A_x(rp)/r$, this says $H_s(b) - \sum_i \theta_i H_\ell(a_i) > 0$ in the direction $\xi$. It is the strict, qualitative form of the paper's Lemma 4.3 ("Transverse slack") at a first cut scale $s$, with the branch Hessian in place of $A_x(sb)$. The paper states that lemma with the quantitative gap $\kappa_g(\ell - s)$. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.critical_hessian_gap`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/CriticalHessianGap.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/CriticalHessianGap.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.critical_hessian_gap)

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

 theorem critical_hessian_gap (hMTW : HasWeakMTW (n := n) (M := M)) (x : M)
    {ξ : TangentSpace (model n) x} (hξ : ξ ≠ 0)
    {S : Set (TangentSpace (model n) x)} (hS : Convex ℝ S)
    {s ℓ : ℝ} (hs : 0 < s) (hsℓ : s < ℓ) (hℓ : ℓ < 1)
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ S, r•a ∈ injectivityDomain x)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b : TangentSpace (model n) x} (hb : b ∈ S) (ha : ∀ i, a i ∈ S)
    (haM : ∀ i, a i ∈ minimizingDomain x)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1) (hbary : ∑ i, θ i • a i = b)
    (horth : ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0)
    (B : ActionBranch (n := n) x (exp x (s•b)))
    (hB : stateChart x (⟨x,s•b⟩ : TangentBundle (model n) M) ∈ B.coord.source) :
    0 < ∑ i, θ i * (branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
