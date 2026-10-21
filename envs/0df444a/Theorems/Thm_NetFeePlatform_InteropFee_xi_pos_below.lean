-- Prove2me | Theorems.Thm_NetFeePlatform_InteropFee_xi_pos_below
-- name    : NetFeePlatform.InteropFee.xi_pos_below
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:27.470982+00:00
-- url     : https://prove2.me/theorems/db5c750f-a73f-48b8-b8dc-25cd4352446a
-- title:
--   Proof of Proposition 7, pp. 52–53 — ξ(t; λ) > 0 for every t < c − 2γ − γλ(J − 1)
-- statement:
--   Let $J \ge 2$, $w \ge 0$, $\gamma \ge 0$ and $\lambda \in [0,1]$. For every net fee
--   $$\tau < c - 2\gamma - \gamma\lambda(J-1)$$
--   we have $\xi(\tau;\lambda) > 0$.
--
--   Together with $\xi(\underline t;\overline\lambda) < 0$ this lets the intermediate value theorem produce a zero of $\xi(\cdot;\overline\lambda)$ below $\underline t$, i.e. a lower symmetric equilibrium net fee.
--
--   **Formalization Note** The paper's chain of inequalities on p. 53 drops the nonnegative term $\gamma\lambda(J-1)(1-n^j)$ in its middle line; the inequality stated here is unaffected. The hypothesis $\gamma \ge 0$ is the paper's standing "network effects are positive" (p. 25).
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), pp. 52–53, Appendix E.2, proof of Proposition 7 (choice of t₋)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropFee_Symmetric

namespace NetFeePlatform.InteropFee
theorem xi_pos_below {J : ℕ} (hJ : 2 ≤ J) (w c γ lam : ℝ) (hw : 0 ≤ w) (hγ : 0 ≤ γ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ∀ τ : ℝ, τ < c - 2 * γ - γ * lam * ((J : ℝ) - 1) → 0 < xi w c γ lam J τ := by sorry
end NetFeePlatform.InteropFee
