-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_compact_first_scale
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.compact_first_scale
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-19T02:59:27.86374+00:00
-- url     : https://prove2.me/theorems/6da9d017-4bd6-4bca-9cd0-cd0cc9d31447
-- title:
--   First scale at which a compact family of velocities leaves the injectivity domain (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact Riemannian manifold modelled on $\mathbb R^n$, with exponential map `exp` and **injectivity domain** $I(x)$ (`injectivityDomain x`), the velocities $v \in T_xM$ whose geodesic $\tau \mapsto \exp_x(\tau v)$ is still minimizing slightly beyond $\tau = 1$. The **minimizing domain** $G_x$ (`minimizingDomain x`, from the definitions bundle `OAIQWMTW002` of this split) is the set of $v$ with $d(x, \exp_x v) = \|v\|$. Points $p$ of the tangent bundle are pairs $(p_1, p_2)$ with $p_2 \in T_{p_1}M$.
--
--   **Statement.** Let $K$ be a compact subset of the tangent bundle, $t_0 > 0$, and $p^0 \in K$ with $t_0\, p^0_2 \notin I(p^0_1)$. Then there is $s$ with $0 < s \le t_0$ such that
--   - $r\, p_2 \in I(p_1)$ for all $0 \le r < s$ and all $p \in K$;
--   - $s\, p_2 \in G_{p_1}$ for all $p \in K$;
--   - some $p \in K$ has $s\, p_2 \notin I(p_1)$.
--
--   So $s$ is the first scale at which the scaled family $sK$ leaves the injectivity domain, and that failure is attained. This is the compactness step at the start of the proof of the paper's Theorem 4.8 ("Global supporting property"), where $K$ is the subgradient graph of a potential. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.compact_first_scale`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/FirstScale.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/FirstScale.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.compact_first_scale)

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

 theorem compact_first_scale {K : Set (TangentBundle (model n) M)} (hK : IsCompact K)
    {t₀ : ℝ} (ht₀ : 0 < t₀) {p₀ : TangentBundle (model n) M} (hp₀ : p₀ ∈ K)
    (hfail : t₀•p₀.2 ∉ injectivityDomain p₀.1) :
    ∃ s : ℝ, 0 < s ∧ s ≤ t₀ ∧
      (∀ r : ℝ, 0 ≤ r → r < s → ∀ p ∈ K, r•p.2 ∈ injectivityDomain p.1) ∧
      (∀ p ∈ K, s•p.2 ∈ minimizingDomain p.1) ∧
      ∃ p ∈ K, s•p.2 ∉ injectivityDomain p.1 := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
