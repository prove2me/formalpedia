-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_activeProjection_critical_bijective
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.activeProjection_critical_bijective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:58:35.6758+00:00
-- url     : https://prove2.me/theorems/3240ac7c-93f2-4b6c-97a1-e352b9392a58
-- title:
--   The projection of the active hull graph stays bijective up to the critical scale (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, with the Riemannian distance $d$, the exponential map $\exp$, the cost $c = d^2/2$, the injectivity domains $I(x)$ (`injectivityDomain`), and the weak MTW condition (`HasWeakMTW`). The weak MTW condition says that the MTW expression $\mathfrak S_{(x,v)}(\xi, \eta)$ (`mtw`) is $\ge 0$ for all $v \in I(x)$ and all orthogonal $\xi, \eta \in T_xM$. The minimizing domain is $G_x = \{w : d(x, \exp_x w) = \|w\|\}$ (`minimizingDomain`). Fix a finite nonempty index set $\iota$, points $y_i$ and numbers $h_i$. The finite potential is $u = \max_i (h_i - c(\cdot, y_i))$. The active hull at $x$ is the convex hull of the minimizing velocities from $x$ to the points $y_i$ that are active at $x$ (`activeHull`). The **active hull graph** $\Gamma$ is the set of pairs $(x, b)$ with $b$ in the active hull at $x$ (`activeHullGraph`). For $s \in \mathbb R$, the **projection** $F_s : \Gamma \to M$ is $F_s(x, b) = \exp_x(s b)$ (`activeProjection`).
--
--   **Statement.** Assume weak MTW. Let $0 < s < 1$, and suppose that
--   - for all $0 \le r < s$ and $(x, b) \in \Gamma$: $r b \in I(x)$;
--   - for all $(x, b) \in \Gamma$: $s b \in G_x$.
--
--   Then $F_s : \Gamma \to M$ is bijective.
--
--   This is the continuation step at the core of the paper's Theorem 4.8 (global supporting property), for finite potentials. Up to the first scale at which a scaled graph vector could leave the injectivity domain, the projection remains a bijection. In the paper this rests on Corollary 3.2 (nonconjugacy of a minimizing convex hull), Lemma 4.5 (surjectivity) and Lemma 4.6 (local injectivity). Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.activeProjection_critical_bijective`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/ActiveContinuation.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/ActiveContinuation.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.activeProjection_critical_bijective)

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

 theorem activeProjection_critical_bijective (y : ι → M) (h : ι → ℝ)
     (hMTW : HasWeakMTW (n := n) (M := M)) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
     (hbelow : ∀ r, 0 ≤ r → r < s → ∀ p ∈ activeHullGraph (n := n) y h,
       r•p.2 ∈ injectivityDomain p.1)
     (hmin : ∀ p ∈ activeHullGraph (n := n) y h, s•p.2 ∈ minimizingDomain p.1) :
     Function.Bijective (activeProjection (n := n) y h s) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
