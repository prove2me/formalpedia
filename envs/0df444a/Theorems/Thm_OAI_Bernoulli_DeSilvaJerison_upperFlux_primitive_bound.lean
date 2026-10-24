-- Prove2me | Theorems.Thm_OAI_Bernoulli_DeSilvaJerison_upperFlux_primitive_bound
-- name    : OAI.Bernoulli.DeSilvaJerison.upperFlux_primitive_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:35:58.465576+00:00
-- url     : https://prove2.me/theorems/ed6c1696-d843-442f-b260-b7f2980814ba
-- title:
--   Pointwise divergence bound for the vertical primitive of the upper calibrating flux of the De Silva–Jerison cone (OpenAI Bernoulli cone)
-- statement:
--   **Notation** (definitions bundle `OAIQWBNS000` of this split). $U$ is the De Silva–Jerison cone on $\mathbb R^7$ (`DeSilvaJerison.U`; see the statement `OAI.Bernoulli.DeSilvaJerison.U_global_minimizer`), and $e_7$ is its axis (`DeSilvaJerison.axis`); $\rho(x)^2 = \lVert x\rVert^2 - x_7^2$ is the squared distance to the axis (`Cylindrical.radiusSq axis x`).
--   - **The upper foliation.** A signed supersolution $S$ (`DeSilvaJerison.upperSigned`) is glued from a smooth cap near the axis (`DeSilvaJerison.smoothCap`) and an outer function (`DeSilvaJerison.outerSigned`). Its dilates $\Phi_\lambda(x) = \kappa\,\lambda\,\max(S(x/\lambda), 0)$ (`DeSilvaJerison.upperFamily`) foliate the region above the graph of $U$: for $t > U(x)$ there is a unique leaf parameter $\lambda(x, t)$ with $\Phi_{\lambda(x,t)}(x) = t$ (`DeSilvaJerison.upperParameter`).
--   - **The flux.** The upper flux (`DeSilvaJerison.upperFlux`) is the field $F(x, t) = \kappa\,\nabla S\bigl(x/\lambda(x,t)\bigr)$ for $t > U(x)$, the gradient of the leaf through $(x, t)$, and $F(x, t) = 0$ for $t \le U(x)$.
--   - **The primitive.** For functions $u \le v$, the vertical potential is $W(x) = 2\int_{u(x)}^{v(x)} F(x, s)\,ds$ (`Foliation.verticalPotential upperFlux u v`), and `Foliation.divergence` is the divergence $\sum_i \langle e_i, DW(x)\,e_i\rangle$.
--   - **The clamp.** The seam height (`DeSilvaJerison.seamHeight`) is $\sigma$, and `Foliation.clampedHeight u σ v` is $\max(u, \min(v, \sigma))$.
--
--   **The statement.** Let $u, v : \mathbb R^7 \to \mathbb R$ with $u \le v$ everywhere, and let $x$ be a point off the axis ($\rho(x) > 0$) with $U(x) < u(x)$. Assume $u$ and $v$ are continuous and differentiable at $x$, and that $\max(u, \min(v, \sigma))$ is differentiable at $x$. Then
--   $$\operatorname{div} W(x) \;\le\; \begin{cases} \lVert\nabla v(x)\rVert^2 + \lVert F(x, u(x))\rVert^2 - 2\,\bigl\langle F(x, u(x)),\, \nabla u(x)\bigr\rangle & \text{if } u(x) < v(x),\\ 0 & \text{otherwise.}\end{cases}$$
--
--   This is the pointwise calibration inequality behind the upper comparison in De Silva and Jerison's proof that $U$ is energy minimizing. Integrated over a ball, the divergence term vanishes and the right side compares the Dirichlet energies of $u$ and $v$.
--
--   Lean: `OAI.Bernoulli.DeSilvaJerison.upperFlux_primitive_bound`, OpenAI's theorem of that name (in `lean/OAI/Analysis/BernoulliCone/PrimitiveBound.lean`).
-- source:
--   OpenAI, The critical dimension for one-phase Bernoulli minimizers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 367; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BernoulliCone/PrimitiveBound.lean (declaration OAI.Bernoulli.DeSilvaJerison.upperFlux_primitive_bound)

import Mathlib
import Definitions.Def_BernoulliNonflatInSeven
import Definitions.Def_OAIQWBNS000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

theorem upperFlux_primitive_bound {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (huv:∀y,u y≤v y)
    (huU:U x<u x) (hqx:0<Cylindrical.radiusSq axis x)
    (hdu:DifferentiableAt ℝ u x) (hdv:DifferentiableAt ℝ v x)
    (hdw:DifferentiableAt ℝ (clampedHeight u seamHeight v) x) :
    divergence (verticalPotential upperFlux u v) x≤
      if u x<v x then ‖gradient v x‖^2+‖upperFlux (x,u x)‖^2-
        2*inner ℝ (upperFlux (x,u x)) (gradient u x) else 0 := by
  sorry
end Bernoulli.DeSilvaJerison

end
end

end OAI
end
