-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_79_82
-- name    : OTCChain.Equilibrium.eq_79_82
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:41.851553+00:00
-- url     : https://prove2.me/theorems/758e451c-7920-4f99-8d1e-77152ab97fb6
-- title:
--   (79)–(82), proof of Theorem 1, Step II, p. 40 (PDF 43) — the equilibrium value functions in closed form
-- statement:
--   Let the standing assumptions hold, $0 < c < c^*$, and let $(\Delta_b,\Delta_s,\mu,V)$ be a steady-state intermediation equilibrium. Then for every $\Delta \in [0,\bar\Delta]$:
--
--   1. $V_n(\Delta)$ equals the constant $V_n$ of (79);
--   2. $V_h(\Delta) = V_h(\Delta_s) + \dfrac{\Delta - \Delta_s}{\kappa + r}$ (81), with $V_h(\Delta_s)$ the constant printed under (82);
--   3. $V(0,\Delta) = \max(V_n(\Delta), V_b(\Delta))$ and $V(1,\Delta) = \max(V_h(\Delta), V_s(\Delta))$ are given by the piecewise formulas (79)–(82): $V(0,\cdot)$ equals $V_n$ on $[0,\Delta_b]$ and $V_n + \int_{\Delta_b}^{\Delta}\frac{dV_b}{dz}dz$ beyond (80); $V(1,\cdot)$ equals $V_s(\Delta_b) + \frac{\Delta - \Delta_b}{\kappa + r + \lambda N_b(1-\eta)}$ on $[0,\Delta_b]$, $V_s(\Delta_b) + \int_{\Delta_b}^\Delta \frac{dV_s}{dz}dz$ on $[\Delta_b,\Delta_s]$ (82) and $V_h(\Delta)$ on $[\Delta_s,\bar\Delta]$ (81).
--
--   The slopes are those of (77)–(78), computed from the closed-form densities (55)–(63) (with the corrected (59)–(60)), and $N_b$, $N_s$ are (66), (64). The value functions determine the prices (6).
--
--   **Formalization Note** The page labels the branches of (80) and (82) "for $z \in \ldots$" where the type $\Delta$ is meant, and its second branch of (82) runs over $(\Delta_b,\bar\Delta]$ although (77) gives no slope of $V_s$ above $\Delta_s$; read with (81), $V(1,\cdot) = V_s$ on $[0,\Delta_s]$ and $V_h$ on $[\Delta_s,\bar\Delta]$. The closed forms are the definitions `candV0`, `candV1`, `candVn`, `candVhAtS` of the ClosedForm module.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 40 (PDF 43), proof of Theorem 1, Step II, (79)–(82)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (79)–(82), proof of Theorem 1, Step II, p. 40: in every intermediation equilibrium (with
`0 < c < c*`), on `[0, ∆̄]`, `Vn` is the constant (79), `Vh` is the line (81) through the
printed `Vh(∆s)`, and `V(0, ·) = max(Vn, Vb)` and `V(1, ·) = max(Vh, Vs)` are the piecewise
formulas (79)–(82) (`candV0`, `candV1`). -/
theorem eq_79_82 (M : Params) (hM : M.Standing) (hc : 0 < M.c) (hcs : M.c < cStar M)
    (Δb Δs : ℝ) (μ : Densities) (V : Values) (hE : IsIntermEq M Δb Δs μ V) :
    ∀ Δ ∈ Icc 0 M.Δbar,
      V.Vn Δ = candVn M Δb Δs ∧
      V.Vh Δ = candVhAtS M Δb Δs + (Δ - Δs) / (M.κ + M.r) ∧
      V.V0 Δ = candV0 M Δb Δs Δ ∧ V.V1 Δ = candV1 M Δb Δs Δ := by sorry

end OTCChain.Equilibrium
