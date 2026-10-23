-- Prove2me | Theorems.Thm_IdentityMgmt_FIA_proposition_1
-- name    : IdentityMgmt.FIA.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:54.698907+00:00
-- url     : https://prove2.me/theorems/ec180014-40cf-415a-bd0a-a1ddc2f6d98e
-- title:
--   Proposition 1, pp. 27–28 (PDF 31–32) — under FIA, active and unserved consumers exist iff c < c̄^FIA, both fractions shrink to 0 as c ↑ c̄^FIA, and type θ_inf gets zero utility
-- statement:
--   Consider the dynamic monopoly with consumer identity management under full information acquisition (FIA): discount factor $\beta$, privacy cost $c$, quasi-linear cut-off rule $\theta_{n+1} = K + \gamma\theta_n$ from $\theta_0 = \tilde\theta$, expectations rule $\Psi(\theta) = C + \lambda\theta$, active consumers $[\tilde\theta, 1]$, and never-served consumers $[0, \theta_{\inf})$ with $\theta_{\inf} = K/(1-\gamma)$. Let
--   $$\bar c^{FIA} = \frac{\beta(1-\gamma)(1+(1-2\beta)\gamma)}{(1-\beta\gamma)^2}.$$
--   Then in every quasi-linear FIA Markov perfect equilibrium:
--
--   1. **(i)** If $c < \bar c^{FIA}$, the set of active customers is non-empty ($\tilde\theta < 1$) and some consumers are left unserved ($\theta_{\inf} > 0$). For two equilibria with the same $\beta$ and privacy costs $c_P < c_Q < \bar c^{FIA}$, both the unserved fraction $\theta_{\inf}$ and the active fraction $1 - \tilde\theta$ are strictly smaller at $c_Q$; and for every $\beta$ and $\varepsilon > 0$ there is $\delta > 0$ such that $\bar c^{FIA} - \delta < c < \bar c^{FIA}$ forces $\theta_{\inf} < \varepsilon$ and $1 - \tilde\theta < \varepsilon$.
--   2. **(ii)** If $c \ge \bar c^{FIA}$, all consumers are passive ($\tilde\theta = 1$) and the market is asymptotically fully covered ($\theta_n \to 0$).
--   3. **(iii)** The lifetime net utility of the marginal customer vanishes in the limit, $\Psi(\theta_n) \to 0$: the customers of type $\theta_{\inf}$ get zero lifetime net utility.
--
--   This is the paper's main analytic result: under FIA, identity management by consumers makes the firm stop expanding the market short of full coverage exactly when privacy is cheap enough.
--
--   **Formalization Note.** The equilibrium is characterized, as in the paper, by the arbitrage equation (8), the first-order condition (16) with the envelope condition (17), and the pivot condition (20) with its corner $\tilde\theta = 1$; the statement holds for every profile satisfying this system, hence for every interior quasi-linear MPE. "Decrease when $c$ increases" compares two equilibria with the same $\beta$ (their $\gamma$ then coincide); $\bar c^{FIA}$ is evaluated at the equilibrium's own $\gamma$. The closed forms (29)–(31) of the Online Appendix are not used: they do not follow from the model as printed.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), pp. 27–28 (PDF 31–32), Proposition 1; Online Appendix, OA p. 5 (PDF 59), proof of Proposition 1

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

namespace IdentityMgmt.FIA

theorem proposition_1 :
    -- (i) below the threshold: active customers exist and some consumers are never served
    (∀ P : Profile, P.IsMPE → P.c < cbarFIA P.β P.γ → P.θt < 1 ∧ 0 < P.θinf) ∧
    -- (i) both fractions decrease when c increases (equilibria with the same β)
    (∀ P Q : Profile, P.IsMPE → Q.IsMPE → P.β = Q.β → P.c < Q.c → Q.c < cbarFIA Q.β Q.γ →
      Q.θinf < P.θinf ∧ 1 - Q.θt < 1 - P.θt) ∧
    -- (i) … and both tend to zero as c approaches the threshold from below
    (∀ β ε : ℝ, 0 < ε → ∃ δ > 0, ∀ P : Profile, P.IsMPE → P.β = β →
      cbarFIA P.β P.γ - δ < P.c → P.c < cbarFIA P.β P.γ → P.θinf < ε ∧ 1 - P.θt < ε) ∧
    -- (ii) at or above the threshold: everyone is passive and the market is asymptotically covered
    (∀ P : Profile, P.IsMPE → cbarFIA P.β P.γ ≤ P.c →
      P.θt = 1 ∧ Filter.Tendsto P.path Filter.atTop (nhds 0)) ∧
    -- (iii) the lifetime net utility of the marginal customer tends to zero along the path
    (∀ P : Profile, P.IsMPE → Filter.Tendsto (fun n => P.Ψ (P.path n)) Filter.atTop (nhds 0)) := by sorry

end IdentityMgmt.FIA
