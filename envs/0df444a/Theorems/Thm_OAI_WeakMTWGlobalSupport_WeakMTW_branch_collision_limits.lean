-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_branch_collision_limits
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:47:10.314465+00:00
-- url     : https://prove2.me/theorems/c384f930-7da5-465a-bd32-30e05c410eb5
-- title:
--   First- and second-order limits along a collision of scaled exponential maps (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact Riemannian manifold modelled on $\mathbb R^n$, with exponential map `exp` and cost $c(x, y) = d(x, y)^2/2$. Fix finitely many targets $y_i \in M$ and heights $h_i$ (a nonempty finite index type). From the definitions bundles of this split:
--   - the potential is $u(x) = \max_i \bigl(h_i - c(x, y_i)\bigr)$ (`finitePotential`), and its **active velocities** at $x$ are the minimizing $a \in T_xM$ with $\exp_x a = y_i$ for an index $i$ attaining the maximum (`activeVelocities`);
--   - an **active representation** $R$ of a tangent vector $p = (p_1, p_2)$ (`ActiveRepresentation y h p`) writes $p_2 = \sum_i \theta_i a_i$ as a convex combination of $\dim M + 1$ active velocities $a_i$ at $p_1$;
--   - the **scaled pole value** is $\|s p_2\|^2/2 + s\,u(p_1)$ (`scaledPoleValue`), and `mulState s p` is $(p_1, s p_2)$;
--   - an **action branch** $B$ from $x$ to $z$ (`ActionBranch x z`) is a smooth local inverse, in the charts at $x$ and $z$, of the pair exponential map. Its value `B.value` is the branch cost.
--
--   **Statement.** Let $0 < \ell < 1$, and let $p_j \to p_0$ in the tangent bundle. Let $q_j$ have base points $q_{j,1} \to p_{0,1}$. Let $s_j \to s$ with $s_j > 0$ eventually, and $(q_{j,1}, s_j q_{j,2}) \to (p_{0,1}, s p_{0,2})$. Suppose that eventually:
--   - the scaled exponentials collide: $\exp_{p_{j,1}}(s_j p_{j,2}) = \exp_{q_{j,1}}(s_j q_{j,2})$;
--   - the scaled pole value of $q_j$ is at most that of $p_j$;
--   - the chart points of $q_{j,1}$ and $p_{j,1}$ at $p_{0,1}$ are distinct, and their normalized difference tends to a direction $e$.
--
--   Let $R_j$ be active representations of $p_j$ whose weights and active velocities converge to those of an active representation $R_0$ of $p_0$, with velocities $a_i$ and weights $\theta_i$. Let $B$ be an action branch from $p_{0,1}$ to $\exp_{p_{0,1}}(s p_{0,2})$ containing the state $(p_{0,1}, s p_{0,2})$. For each $i$, let $C_i$ be an action branch from $p_{0,1}$ to $\exp_{p_{0,1}}(\ell a_i)$ containing the state $(p_{0,1}, \ell a_i)$. Write $\partial_e$ for the derivative in the first endpoint in the direction $(e, 0)$, at the chart points of the base point and the respective endpoint. Then
--   $$\partial_e B - \tfrac{s}{\ell}\,\partial_e C_i \le 0 \ \text{ for every } i, \qquad \sum_i \theta_i\bigl(\partial_e^2 B - \tfrac{s}{\ell}\,\partial_e^2 C_i\bigr) \le 0 .$$
--
--   These are the limits $d_i \le 0$ and the second-order inequality obtained by dividing the paper's expansion (4.8) by $l_j$ and by $l_j^2$, after cancelling the linear terms with (4.9), in the proof of Lemma 4.6 ("Local injectivity of the projection"). Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/BranchCollisionLimits.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/BranchCollisionLimits.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits)

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
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem branch_collision_limits (y : ι → M) (h : ι → ℝ)
    {p q : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto (fun j => (q j).1) atTop (𝓝 p₀.1))
    {sⱼ : ℕ → ℝ} {s ℓ : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s))
    (hqp : Tendsto (fun j => mulState (sⱼ j) (q j)) atTop (𝓝 (mulState s p₀)))
    (hpos : ∀ᶠ j in atTop, 0 < sⱼ j) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    (hcollision : ∀ᶠ j in atTop, exp (p j).1 (sⱼ j•(p j).2) = exp (q j).1 (sⱼ j•(q j).2))
    (hvalue : ∀ᶠ j in atTop, scaledPoleValue y h (sⱼ j) (q j) ≤ scaledPoleValue y h (sⱼ j) (p j))
    (R : ∀ j, ActiveRepresentation y h (p j)) (R₀ : ActiveRepresentation y h p₀)
    (hθ : ∀ i, Tendsto (fun j => (R j).θ i) atTop (𝓝 (R₀.θ i)))
    (ha : ∀ i, Tendsto (fun j => (⟨(p j).1,(R j).a i⟩ : TangentBundle (model n) M))
      atTop (𝓝 ⟨p₀.1,R₀.a i⟩))
    (B : ActionBranch (n := n) p₀.1 (exp p₀.1 (s•p₀.2)))
    (hB : stateChart p₀.1 (mulState s p₀) ∈ B.coord.source)
    (C : ∀ i, ActionBranch (n := n) p₀.1 (exp p₀.1 (ℓ•R₀.a i)))
    (hC : ∀ i, stateChart p₀.1 (⟨p₀.1,ℓ•R₀.a i⟩ : TangentBundle (model n) M) ∈ (C i).coord.source)
    {e : Model n}
    (hd : Tendsto (fun j => NormedSpace.normalize
      (chartAt (Model n) p₀.1 (q j).1 - chartAt (Model n) p₀.1 (p j).1)) atTop (𝓝 e))
    (hne : ∀ᶠ j in atTop, chartAt (Model n) p₀.1 (q j).1 ≠ chartAt (Model n) p₀.1 (p j).1) :
    (∀ i, fderiv ℝ B.value (chartAt (Model n) p₀.1 p₀.1,
        chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp p₀.1 (s•p₀.2))) (e,0) -
      (s/ℓ)*fderiv ℝ (C i).value (chartAt (Model n) p₀.1 p₀.1,
        chartAt (Model n) (exp p₀.1 (ℓ•R₀.a i)) (exp p₀.1 (ℓ•R₀.a i))) (e,0) ≤ 0) ∧
    (∑ i, R₀.θ i*(fderiv ℝ (fderiv ℝ B.value)
      (chartAt (Model n) p₀.1 p₀.1,chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp p₀.1 (s•p₀.2))) (e,0) (e,0) -
      (s/ℓ)*fderiv ℝ (fderiv ℝ (C i).value)
        (chartAt (Model n) p₀.1 p₀.1,chartAt (Model n) (exp p₀.1 (ℓ•R₀.a i)) (exp p₀.1 (ℓ•R₀.a i))) (e,0) (e,0))) ≤ 0 := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
