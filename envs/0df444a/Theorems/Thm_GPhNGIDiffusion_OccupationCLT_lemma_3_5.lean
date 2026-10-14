-- Prove2me | Theorems.Thm_GPhNGIDiffusion_OccupationCLT_lemma_3_5
-- name    : GPhNGIDiffusion.OccupationCLT.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:06.062565+00:00
-- url     : https://prove2.me/theorems/c5433edd-6291-4acb-a13c-e5e2081d31aa
-- title:
--   Lemma 3.5, p. 14 — ∥J^{ε,x}_{s,t} − J^x_{s,t}∥_op → 0 almost surely as ε → 0
-- statement:
--   Let $J^{\varepsilon,x}_{s,t}$ be the Jacobian of the mollified diffusion, i.e. the propagator of $\partial_tJ=\nabla g_\varepsilon(X^{\varepsilon,x}_t)J$, and $J^x_{s,t}$ the propagator of $\partial_tJ=\nabla\tilde g(X^x_t)J$, both with $J_{s,s}=I$. For every $x\in\mathbb R^d$, almost surely
--   $$
--   \|J^{\varepsilon,x}_{s,t}-J^x_{s,t}\|_{op}\to0\qquad(\varepsilon\to0)\quad\text{for all }0\le s\le t<\infty.
--   $$
--
--   This identifies $J^x$ as the derivative flow of the non-smooth diffusion.
--
--   **Formalization Note** The Jacobians are propagators of the linear equations rather than the paper's $\exp(\int_s^t\cdot\,dr)$, which is not the solution when the matrices do not commute (see the `Jacobian` definition). "a.s." is read with one null set for all $0\le s\le t<\infty$: the proof (pp. 32–33) fixes the event $N$ of (B.7) and shows convergence for every $(s,t)$ off it.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 14, Lemma 3.5 (proof pp. 32–33)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Diffusion
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Jacobian
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

/-- Lemma 3.5, p. 14. `J^{ε,x}_{s,t}` and `J^x_{s,t}` are the propagators of
`∂ₜJ = ∇g_ε(X^{ε,x}_t)J` and `∂ₜJ = ∇g̃(X^x_t)J` (`J_{s,s} = I`). For every `x`, almost
surely, `‖J^{ε,x}_{s,t} − J^x_{s,t}‖_op → 0` as `ε → 0` for all `0 ≤ s ≤ t < ∞` (one null set
for all `(s, t)`, as in the proof, pp. 32–33). -/
theorem lemma_3_5 {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X)
    (Xε : ℝ → E d → ℝ≥0 → Ω → E d)
    (hXε : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, IsSolution (M.gEps ε) M.σ B (Xε ε))
    (Jε : ℝ → E d → ℝ≥0 → ℝ≥0 → Ω → (E d →L[ℝ] E d))
    (hJε : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ x ω,
      IsPropagator (fun r => M.gradEps ε (Xε ε x r ω)) (fun s t => Jε ε x s t ω))
    (J : E d → ℝ≥0 → ℝ≥0 → Ω → (E d →L[ℝ] E d))
    (hJ : ∀ x ω, IsPropagator (fun r => M.gradTilde (X x r ω)) (fun s t => J x s t ω)) :
    ∀ x : E d, ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      Tendsto (fun ε : ℝ => ‖Jε ε x s t ω - J x s t ω‖) (𝓝[>] 0) (𝓝 0) := by sorry

end GPhNGIDiffusion.OccupationCLT
