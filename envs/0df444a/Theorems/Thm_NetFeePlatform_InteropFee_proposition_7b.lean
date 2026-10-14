-- Prove2me | Theorems.Thm_NetFeePlatform_InteropFee_proposition_7b
-- name    : NetFeePlatform.InteropFee.proposition_7b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:18.374725+00:00
-- url     : https://prove2.me/theorems/f65a82cd-b569-473a-82a0-7745fbc533f3
-- title:
--   Proposition 7(b), p. 26 — stronger interoperability gives a lower symmetric equilibrium net fee, except in duopoly without outside option, where the net fee is unchanged (Logit, 0 < γ ≤ 27/8)
-- statement:
--   Consider $J \ge 2$ ex ante identical platforms with Logit demand $n^j = e^{-t^j}/(w + \sum_k e^{-t^k})$, outside-option weight $w = e^{z} \ge 0$ ($w = 0$: no outside option), common marginal cost $c$ and interaction value $\gamma$ with $0 < \gamma \le 27/8$. Let $0 \le \underline\lambda < \overline\lambda \le 1$ be two interoperability levels, and suppose that the profile in which every platform charges the net fee $\underline t$ is a pure-strategy Nash equilibrium in net fees under $\lambda = \underline\lambda$. Then:
--
--   1. **duopoly with outside option, or $J \ge 3$** ($w > 0$ or $J \ge 3$): there is a net fee $\overline t < \underline t$ such that the profile in which every platform charges $\overline t$ is a Nash equilibrium under $\lambda = \overline\lambda$;
--   2. **duopoly without outside option** ($J = 2$, $w = 0$): the profile in which both platforms charge $\underline t$ is still a Nash equilibrium under $\lambda = \overline\lambda$, i.e. $\overline t = \underline t$.
--
--   The result says that the users' gain from interoperability is not eaten up by softer competition: the extra off-network interaction utility platforms can extract dominates, so the equilibrium net fee falls — except in a duopoly without outside option, where the two effects exactly balance.
--
--   **Formalization Note** The paper states Proposition 7 for general demand; this mission formalizes the Logit case (13), the specification of §5–6, because the paper's proof writes the Logit markup $1/(1-n^j)$ and its general-demand sufficiency argument is only sketched (Appendix E.1.3). Two hypotheses are added. $\gamma > 0$: the proof needs positive network effects ("as long as network effects are positive", p. 25); with $\gamma < 0$ the comparison reverses. $\gamma \le 27/8$: the paper proves that a zero of $\xi$ is an equilibrium only under the bound (36) (Proposition 2′'s 3.375). The range $\underline\lambda,\overline\lambda \in [0,1]$ comes from part (a). "There is a symmetric equilibrium with $\overline t = \underline t$" is encoded as "the constant profile $\underline t$ is an equilibrium under $\overline\lambda$".
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 26, Proposition 7(b); proof pp. 52–53 (Appendix E.2)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropFee
theorem proposition_7b {J : ℕ} (hJ : 2 ≤ J) (w c γ lamLo lamHi tLo : ℝ) (hw : 0 ≤ w)
    (hγ : 0 < γ) (hγ' : γ ≤ 27 / 8) (hlo : 0 ≤ lamLo) (hlt : lamLo < lamHi) (hhi : lamHi ≤ 1)
    (htLo : NetFeePlatform.Competition.IsEquilibrium w c γ lamLo (fun _ : Fin J => tLo)) :
    ((3 ≤ J ∨ 0 < w) → ∃ tHi : ℝ, tHi < tLo ∧ NetFeePlatform.Competition.IsEquilibrium w c γ lamHi (fun _ : Fin J => tHi)) ∧
      (J = 2 → w = 0 → NetFeePlatform.Competition.IsEquilibrium w c γ lamHi (fun _ : Fin J => tLo)) := by sorry
end NetFeePlatform.InteropFee
