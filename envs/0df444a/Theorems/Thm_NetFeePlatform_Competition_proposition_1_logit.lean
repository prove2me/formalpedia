-- Prove2me | Theorems.Thm_NetFeePlatform_Competition_proposition_1_logit
-- name    : NetFeePlatform.Competition.proposition_1_logit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:07.679488+00:00
-- url     : https://prove2.me/theorems/5ce2c764-8f25-4c4b-9483-49609fea2fdd
-- title:
--   Proposition 1 in Logit form (14), p. 13 — at any equilibrium, tʲ = c + 1/(1 − nʲ) − 2γnʲ
-- statement:
--   Consider the one-sided Logit platform game with $J$ platforms, outside-option weight $w\ge0$, common marginal cost $c$, common interaction value $\gamma$ and no interoperability: platform $j$'s profit is $\pi^j(t)=(t^j+\gamma n^j(t)-c)\,n^j(t)$ with $n^j(t)=e^{-t^j}/(w+\sum_k e^{-t^k})$. Assume that either there is an outside option ($w>0$) or there are at least two platforms ($J\ge2$).
--
--   If $t$ is a pure-strategy Nash equilibrium in net fees, then every platform's net fee satisfies
--   $$t^j=c+\frac{1}{1-n^j(t)}-2\gamma\,n^j(t).$$
--
--   This is the Logit, one-sided form (14) of the general pricing formula (12) of Proposition 1: marginal cost, plus the one-sided market-power term $n^j/(-\partial n^j/\partial t^j)=1/(1-n^j)$, minus the network discount $(\gamma+\gamma)n^j$.
--
--   **Formalization Note** With one side and $\gamma^j_{ss}=\gamma$, the sum $\sum_{\hat s}(\gamma^j_{s\hat s}+\gamma^j_{\hat s s})n^j_{\hat s}$ of (12) is $2\gamma n^j$. The hypothesis "$w>0$ or $J\ge2$" is the paper's "either $J\ge2$ or users have an outside option" (Proposition 2′); it guarantees $n^j<1$ (with $w=0$ and $J=1$ the monopolist's profit is unbounded and no equilibrium exists).
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 12, Proposition 1, (12); p. 13, (14)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.Competition
theorem proposition_1_logit {J : ℕ} (w c γ : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (t : Fin J → ℝ) (ht : IsEquilibrium w c γ 0 t) :
    ∀ j, t j = c + 1 / (1 - demand w t j) - 2 * γ * demand w t j := by sorry
end NetFeePlatform.Competition
