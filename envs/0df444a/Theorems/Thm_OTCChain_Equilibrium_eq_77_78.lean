-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_77_78
-- name    : OTCChain.Equilibrium.eq_77_78
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:37.015983+00:00
-- url     : https://prove2.me/theorems/c7ba8b7b-dbbc-457a-a421-e180f17e0496
-- title:
--   (77)–(78), proof of Theorem 1, Step II, p. 40 (PDF 43) — the slopes of V_s and V_b in equilibrium
-- statement:
--   Let the standing assumptions hold, $0 < c < c^*$, and let $(\Delta_b,\Delta_s,\mu,V)$ be a steady-state intermediation equilibrium (Definition 1). Let $N_b$, $N_s$ be its populations, $F_s(\Delta) = \int_0^\Delta\mu_s$, $F_b(\Delta) = \int_0^\Delta\mu_b$ and
--   $$D(\Delta) = \kappa + r + \lambda(1-\eta)[N_b - F_b(\Delta)] + \lambda\eta F_s(\Delta).$$
--   Then $V_s$ and $V_b$ are differentiable with
--   $$\frac{dV_s}{d\Delta} = \begin{cases}\dfrac{1}{\kappa + r + \lambda(1-\eta)N_b} & \Delta \in (0,\Delta_b),\\[2mm] \dfrac{1}{\kappa+r}\dfrac{\kappa + r + \lambda\eta F_s(\Delta)}{D(\Delta)} & \Delta \in (\Delta_b,\Delta_s),\end{cases}\qquad \frac{dV_b}{d\Delta} = \begin{cases}\dfrac{1}{\kappa+r}\dfrac{\lambda\eta F_s(\Delta)}{D(\Delta)} & \Delta \in (\Delta_b,\Delta_s),\\[2mm] \dfrac{1}{\kappa+r}\dfrac{\lambda\eta N_s}{\kappa + r + \lambda\eta N_s} & \Delta \in (\Delta_s,\bar\Delta).\end{cases}$$
--
--   These slopes, integrated, give the value functions (79)–(82).
--
--   **Formalization Note** The page states the first branch of (77) on $[0,\Delta_b)$ and the second branch of (78) on $(\Delta_s,\bar\Delta]$; the value functions are only constrained on $[0,\bar\Delta]$, so two-sided derivatives are stated on the open intervals.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 40 (PDF 43), proof of Theorem 1, Step II, (77)–(78)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (77)–(78), proof of Theorem 1, Step II, p. 40: in every intermediation equilibrium (with
`0 < c < c*`), `Vs` and `Vb` are differentiable on the open pieces with the slopes
(77) `dVs/d∆ = 1/(κ + r + λ(1 − η)N_b)` on `(0, ∆b)` and the middle branch on `(∆b, ∆s)`;
(78) the middle branch on `(∆b, ∆s)` and `dVb/d∆ = (1/(κ + r)) λη N_s/(κ + r + λη N_s)` on
`(∆s, ∆̄)`. Here `N_b`, `N_s`, `F_b`, `F_s` are those of the equilibrium densities. -/
theorem eq_77_78 (M : Params) (hM : M.Standing) (hc : 0 < M.c) (hcs : M.c < cStar M)
    (Δb Δs : ℝ) (μ : Densities) (V : Values) (hE : IsIntermEq M Δb Δs μ V) :
    (∀ Δ ∈ Ioo 0 Δb, HasDerivAt V.Vs (slopeVsLow M μ) Δ) ∧
    (∀ Δ ∈ Ioo Δb Δs, HasDerivAt V.Vs (slopeVsMid M μ Δ) Δ) ∧
    (∀ Δ ∈ Ioo Δb Δs, HasDerivAt V.Vb (slopeVbMid M μ Δ) Δ) ∧
    (∀ Δ ∈ Ioo Δs M.Δbar, HasDerivAt V.Vb (slopeVbHigh M μ) Δ) := by sorry

end OTCChain.Equilibrium
