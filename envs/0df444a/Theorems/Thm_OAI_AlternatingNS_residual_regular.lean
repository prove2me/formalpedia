-- Prove2me | Theorems.Thm_OAI_AlternatingNS_residual_regular
-- name    : OAI.AlternatingNS.residual_regular
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-12T01:22:07.740375+00:00
-- url     : https://prove2.me/theorems/9e1e51f1-3578-4635-8c97-f1c778f61e8a
-- title:
--   The Navier–Stokes residual of a smooth, rapidly decaying, compactly supported velocity is smooth, compactly supported and rapidly decaying
-- statement:
--   Let $\nu\in\mathbb R$, let $K\subset\mathbb R^3$ be compact and let $U$ be smooth on $[0,\infty)\times\mathbb R^3$, spatially supported in $K$ and rapidly decaying with all derivatives. Then the force
--   $$f=\partial_tU+(U\cdot\nabla)U-\nu\Delta U$$
--   is smooth on $[0,\infty)\times\mathbb R^3$, spatially supported in $K$, and rapidly decaying with all derivatives.
--
--   Smoothness holds because the one-sided time derivative and the spatial derivatives of a smooth function on the closed half-space are smooth there. The support claim holds because $U(t,\cdot)$ vanishes on the open set $\mathbb R^3\setminus K$. Rapid decay follows from the Leibniz rule: every derivative of $(U\cdot\nabla)U$ is a sum of products of derivatives of $U$, each rapidly decaying.
--
--   **Formalization Note** Fields are functions $\mathbb R\to\mathbb R^3\to E$ (`Field`); only $t\ge0$ matters. `Smooth` is $C^\infty$ on $[0,\infty)\times\mathbb R^3$, `Rapid` bounds $(1+t+\|x\|)^J\|\partial_t^l\partial_x^\alpha F\|$ for all $J,l,\alpha$, `SupportedIn F K` means $\operatorname{supp}F(t,\cdot)\subseteq K$ for $t\ge0$, `residual ν U` is $\partial_tU+(U\cdot\nabla)U-\nu\Delta U$, and time derivatives are taken within $[0,\infty)$. All notions are those of the published definition `NavierStokesAlternating`.
-- source:
--   OpenAI, "Computation under Rapidly Vanishing Navier–Stokes Forcing" (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf; goal theorem OAI.AlternatingNS.alternating of the mission "Computation under Rapidly Vanishing Navier–Stokes Forcing"

import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **The Navier–Stokes residual inherits regularity.** If `U` is smooth, rapidly decaying and
spatially supported in a compact set `K`, then so is the force `f = ∂ₜU + (U·∇)U − νΔU`. -/
theorem residual_regular (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U) :
    Smooth (residual ν U) ∧ SupportedIn (residual ν U) K ∧ Rapid (residual ν U) := by
  sorry

end AlternatingNS
end OAI
