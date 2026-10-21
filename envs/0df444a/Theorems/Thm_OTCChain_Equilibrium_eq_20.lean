-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_eq_20
-- name    : OTCChain.Equilibrium.eq_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:58.016616+00:00
-- url     : https://prove2.me/theorems/0c45b50e-f7e4-471f-a214-531b5cd61abe
-- title:
--   (20), proof of Theorem 1, Step II, pp. 40–41 (PDF 43–44) — the buyer-cutoff equation has a unique root, and every equilibrium's Δ_b solves it
-- statement:
--   Let the standing assumptions hold and let
--   $$\mathrm{rhs}_{20}(\delta) = \frac{\lambda\kappa\eta X}{[\kappa + r + \lambda N_b(1-\eta)](\kappa + \lambda N_b)}\int_0^\delta F(x)\,dx, \qquad N_b = N_b(F(\delta)) \text{ from (66)}.$$
--   Then
--
--   1. $\mathrm{rhs}_{20}(0) = 0$ and $\mathrm{rhs}_{20}$ is nondecreasing on $[0,\bar\Delta]$;
--   2. for every $0 < c \le \mathrm{rhs}_{20}(\bar\Delta)$ the equation $c = \mathrm{rhs}_{20}(\Delta_b)$ has exactly one solution $\Delta_b \in [0,\bar\Delta]$;
--   3. if the search cost satisfies $0 < c < c^*$, then in every steady-state intermediation equilibrium the buyer cutoff solves (20): $c = \mathrm{rhs}_{20}(\Delta_b)$. This is the indifference condition $V_b(\Delta_b) = V_n$.
--
--   **Formalization Note** The page asserts a unique solution in $[0,\bar\Delta]$ from "monotonicity and boundary conditions"; the solution exists only for $c \le \mathrm{rhs}_{20}(\bar\Delta)$, and for $c = 0$ it need not be unique (when $F$ vanishes near $0$), so the range $0 < c \le \mathrm{rhs}_{20}(\bar\Delta)$ is stated. Both bounds hold when $0 < c < c^*$.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), pp. 40–41 (PDF 43–44), proof of Theorem 1, Step II, (20); (20) stated p. 13 (PDF 16)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- (20), proof of Theorem 1, Step II, pp. 40–41: the right-hand side of (20) vanishes at
`∆b = 0` and is nondecreasing on `[0, ∆̄]`; for every `0 < c ≤ rhs20(∆̄)` the equation
`c = rhs20(∆b)` has exactly one solution in `[0, ∆̄]`; and in every intermediation equilibrium
(with `0 < c < c*`) the buyer cutoff solves (20), i.e. `rhs20(∆b) = c` (indifference
`Vb(∆b) = Vn`). -/
theorem eq_20 (M : Params) (hM : M.Standing) :
    rhs20 M 0 = 0 ∧ MonotoneOn (rhs20 M) (Icc 0 M.Δbar) ∧
    (∀ c : ℝ, 0 < c → c ≤ rhs20 M M.Δbar → ∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs20 M δ = c) ∧
    (0 < M.c → M.c < cStar M → ∀ (Δb Δs : ℝ) (μ : Densities) (V : Values),
      IsIntermEq M Δb Δs μ V → rhs20 M Δb = M.c) := by sorry

end OTCChain.Equilibrium
