-- Prove2me | Theorems.Thm_NetFeePlatform_InteropFee_proposition_7a
-- name    : NetFeePlatform.InteropFee.proposition_7a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:21.038974+00:00
-- url     : https://prove2.me/theorems/50b63175-a0b7-43e2-917a-8cc6b055ed0f
-- title:
--   Proposition 7(a), p. 26 — at a symmetric equilibrium, t = c + 1/(1 − nʲ) − (2 + λ(J − 1 − φʲ))γnʲ (Logit form of (21))
-- statement:
--   Let $J \ge 2$ platforms with Logit demand, outside-option weight $w \ge 0$, common marginal cost $c$, interaction value $\gamma$ and interoperability $\lambda \in [0,1]$. Suppose the constant profile in which every platform charges the net fee $\tau$ is a pure-strategy Nash equilibrium in net fees. Writing $n = n(\tau)$ for the common share and $\varphi = \varphi(\tau)$ for the common diversion ratio,
--   $$\tau = c + \frac{1}{1-n} - \big(2 + \lambda(J - 1 - \varphi)\big)\gamma\, n.$$
--
--   This is the paper's pricing formula (21) in its Logit form, where the markup $n^j/(-\partial n^j/\partial t^j)$ equals $1/(1-n^j)$. Compared to the case without interoperability, the factor $\lambda(J-1-\varphi)$ is new: it balances the off-network interaction utility the platform extracts from new users against the revenue lost when users are diverted from rivals.
--
--   **Formalization Note** Proposition 7 is stated in the paper for general demand; this mission formalizes the Logit case (13) with outside-option weight $w = e^{z} \ge 0$, the specification of the paper's §5–6. The equilibrium is the global Nash condition, so the statement includes the first-order necessity argument.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 26, Proposition 7(a), (21); p. 52, proof of Proposition 7 (via (33), p. 39)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropFee_Symmetric

namespace NetFeePlatform.InteropFee
theorem proposition_7a {J : ℕ} (hJ : 2 ≤ J) (w c γ lam τ : ℝ) (hw : 0 ≤ w)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (ht : NetFeePlatform.Competition.IsEquilibrium w c γ lam (fun _ : Fin J => τ)) :
    τ = c + 1 / (1 - nSym w J τ) - (2 + lam * ((J : ℝ) - 1 - phiSym w J τ)) * γ * nSym w J τ := by sorry
end NetFeePlatform.InteropFee
