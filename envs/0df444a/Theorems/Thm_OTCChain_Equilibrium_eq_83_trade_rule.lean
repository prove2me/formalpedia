-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_83_trade_rule
-- name    : OTCChain.Equilibrium.eq_83_trade_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:38.075968+00:00
-- url     : https://prove2.me/theorems/9549561b-fb22-4a73-9b11-b85222dd62d7
-- title:
--   (83) and (7), proof of Theorem 1, Step II, p. 40 (PDF 43) — S(x, y) is the integral of ξ, so trade occurs iff the buyer's type exceeds the seller's
-- statement:
--   Let the standing assumptions hold, $0 < c < c^*$, and let $(\Delta_b,\Delta_s,\mu,V)$ be a steady-state intermediation equilibrium. Define on $(\Delta_b,\Delta_s)$
--   $$\xi(\Delta) = \frac{dV_s(\Delta)}{d\Delta} - \frac{dV_b(\Delta)}{d\Delta}, \qquad (83)$$
--   with the middle branches of (77)–(78). Then
--
--   1. for $x, y \in (\Delta_b,\Delta_s)$, $S(x,y) = \int_y^x \xi(z)\,dz$;
--   2. (7) for every buyer type $x \in (\Delta_b,\bar\Delta]$ and seller type $y \in [0,\Delta_s)$, $S(x,y) > 0$ if and only if $x > y$.
--
--   This is the trade rule the paper conjectures in (7): a meeting results in a trade exactly when the buyer's type exceeds the seller's. In the formalization it is a conclusion about every equilibrium, not an assumption built into the Bellman system.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 40 (PDF 43), proof of Theorem 1, Step II, (83) and the verification of (7); (7) stated p. 9 (PDF 12)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (83) and (7), proof of Theorem 1, Step II, p. 40: in every intermediation equilibrium (with
`0 < c < c*`), for `x, y ∈ (∆b, ∆s)` the surplus is `S(x, y) = ∫_y^x ξ` with
`ξ = dVs/d∆ − dVb/d∆` (middle branches of (77)–(78)), and for every buyer type
`x ∈ (∆b, ∆̄]` and seller type `y ∈ [0, ∆s)`, `S(x, y) > 0` iff `x > y`. -/
theorem eq_83_trade_rule (M : Params) (hM : M.Standing) (hc : 0 < M.c) (hcs : M.c < cStar M)
    (Δb Δs : ℝ) (μ : Densities) (V : Values) (hE : IsIntermEq M Δb Δs μ V) :
    (∀ x ∈ Ioo Δb Δs, ∀ y ∈ Ioo Δb Δs,
      surplus V x y = ∫ z in y..x, (slopeVsMid M μ z - slopeVbMid M μ z)) ∧
    (∀ x ∈ Ioc Δb M.Δbar, ∀ y ∈ Ico 0 Δs, 0 < surplus V x y ↔ y < x) := by sorry

end OTCChain.Equilibrium
