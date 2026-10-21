-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_proposition_2
-- name    : InvIntegration.Behavioral.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:13.195042+00:00
-- url     : https://prove2.me/theorems/ff30d735-953f-4f77-9424-e70972059c47
-- title:
--   Proposition 2, pp. 10–11 (PDF 10–11) — best response q∗(ṽ) = Ḡ(ṽ)(m + ẑ·sd) is the unique maximizer, with profit Ḡ(ṽ)Π(m, sd)
-- statement:
--   Consider a market with normal demand $D\sim N(m,\mathrm{sd}^2)$, $m>0$, $\mathrm{sd}>0$, and let the firm believe the critical valuation is $\tilde v$. Then the inventory level
--   $$q^*(\tilde v) = \bar G(\tilde v)\,(m + \hat z\,\mathrm{sd})$$
--   is the unique maximizer of the expected profit $\pi(q)=\mathbb E[(p-s)\min(q,\bar G(\tilde v)D)-(c-s)q]$, and
--   $$\pi\bigl(q^*(\tilde v)\bigr) = \bar G(\tilde v)\,\Pi(m,\mathrm{sd}).$$
--
--   Part (i) of the paper is the case $m=\mu$, $\mathrm{sd}=\sigma$ (multichannel), and part (ii) the case $m=2\mu$, $\mathrm{sd}=\sqrt{2(1+\rho)}\,\sigma$ (integrated). It is the firm's best-response function in the firm–consumer game.
--
--   **Formalization Note.** The statement is generic in the market $(m,\mathrm{sd})$; the paper's two parts are its two instances.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), pp. 10–11 (PDF 10–11), Proposition 2 (i)–(ii)

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem proposition_2 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (vt : ℝ) :
    (∀ q : ℝ, q ≠ Gbar P vt * (m + P.zh * sd) →
      profit P m sd vt q < profit P m sd vt (Gbar P vt * (m + P.zh * sd))) ∧
    profit P m sd vt (Gbar P vt * (m + P.zh * sd)) = Gbar P vt * Pi P m sd := by sorry

end InvIntegration.Behavioral
