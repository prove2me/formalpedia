-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_critical_collision_sequence_false
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.critical_collision_sequence_false
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:59:06.92121+00:00
-- url     : https://prove2.me/theorems/c08ccfed-83e1-4cb7-8d76-2ac9cffc2861
-- title:
--   No collision sequence at a nonconjugate scale under weak MTW (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statement `OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits` of this split. $M$ is a compact Riemannian manifold, with finitely many targets $y_i$ and heights $h_i$ (a nonempty finite index type) defining the potential $u = \max_i (h_i - c(\cdot, y_i))$. The active hull at $x$ (`activeHull y h x`) is the convex hull of the active velocities at $x$, and `activeHullGraph y h` is the set of tangent vectors $p$ with $p_2$ in the active hull at $p_1$. The scaled pole value of $p$ at scale $s$ is $\|s p_2\|^2/2 + s\,u(p_1)$ (`scaledPoleValue`), and `mulState s p` is $(p_1, s p_2)$. From the published goal bundle come the injectivity domain $I(x)$ and the weak MTW condition (`HasWeakMTW`). A velocity $v \in T_xM$ is **nonconjugate** (`Nonconjugate x v`) if the derivative of $w \mapsto \exp_x w$ at $v$, read in a chart at $\exp_x v$, is injective.
--
--   **Statement.** Assume weak MTW. Let $p_j \to p_0$ be points of the active hull graph, and let $q_j$ be tangent vectors with base points $q_{j,1} \to p_{0,1}$. Let $s_j \to s$ with $s_j > 0$ eventually and $0 \le s < 1$, and $(q_{j,1}, s_j q_{j,2}) \to (p_{0,1}, s p_{0,2})$. Suppose that eventually $p_j \neq q_j$, the scaled exponentials collide, $\exp_{p_{j,1}}(s_j p_{j,2}) = \exp_{q_{j,1}}(s_j q_{j,2})$, and the scaled pole value of $q_j$ at $s_j$ is at most that of $p_j$. Suppose further that $r a \in I(p_{0,1})$ for all $0 \le r < s$ and all $a$ in the active hull at $p_{0,1}$, and that $s\,p_{0,2}$ is nonconjugate at $p_{0,1}$. Then this situation is impossible: the conclusion is `False`.
--
--   This is the contradiction at the heart of the proof of the paper's Lemma 4.6 ("Local injectivity of the projection"): a failure of local injectivity of $(x, p) \mapsto \exp_x(sp)$ on the active hull graph would produce such a collision sequence. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.critical_collision_sequence_false`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/CriticalCollision.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/CriticalCollision.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.critical_collision_sequence_false)

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

 theorem critical_collision_sequence_false (y : ι → M) (h : ι → ℝ)
    (hMTW : HasWeakMTW (n := n) (M := M))
    {p q : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto (fun j => (q j).1) atTop (𝓝 p₀.1))
    {sⱼ : ℕ → ℝ} {s : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s))
    (hqp : Tendsto (fun j => mulState (sⱼ j) (q j)) atTop (𝓝 (mulState s p₀)))
    (hpos : ∀ᶠ j in atTop, 0 < sⱼ j) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hg : ∀ j, p j ∈ activeHullGraph y h)
    (hne : ∀ᶠ j in atTop, p j ≠ q j)
    (hcollision : ∀ᶠ j in atTop, exp (p j).1 (sⱼ j•(p j).2) = exp (q j).1 (sⱼ j•(q j).2))
    (hvalue : ∀ᶠ j in atTop, scaledPoleValue y h (sⱼ j) (q j) ≤ scaledPoleValue y h (sⱼ j) (p j))
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ activeHull (n := n) y h p₀.1, r•a ∈ injectivityDomain p₀.1)
    (hn : Nonconjugate p₀.1 (s•p₀.2)) : False := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
