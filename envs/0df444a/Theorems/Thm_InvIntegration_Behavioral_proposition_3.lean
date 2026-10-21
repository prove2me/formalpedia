-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_proposition_3
-- name    : InvIntegration.Behavioral.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:55.566477+00:00
-- url     : https://prove2.me/theorems/c30504df-68eb-48a4-ac84-4b877d47da7d
-- title:
--   Proposition 3, p. 11 (PDF 11) — a unique equilibrium exists, and v∗ < vh
-- statement:
--   For every market with normal demand $N(m,\mathrm{sd}^2)$, $m>0$, $\mathrm{sd}>0$, the firm–consumer game of Definition 1 has an equilibrium $(q^*,v^*,\xi^*)$ with
--   $$v^* < v_h,$$
--   and any two equilibria coincide.
--
--   This applies to both systems: the multichannel market $N(\mu,\sigma^2)$ and the integrated market $N(2\mu,2(1+\rho)\sigma^2)$. It makes $v^*_m$ and $v^*_I$, the equilibrium threshold valuations, well defined, which every later result uses.
--
--   **Formalization Note.** Symmetry of the multichannel equilibrium across the two markets is built into the encoding (the two markets are identical, so one market is formalized). The δ-monotonicity sentences of Proposition 3 are not formalized.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), p. 11 (PDF 11), Proposition 3 (first two sentences)

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem proposition_3 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd) :
    (∃ q v ξ : ℝ, IsEquilibrium P m sd q v ξ ∧ v < P.vh) ∧
    (∀ q v ξ q' v' ξ' : ℝ, IsEquilibrium P m sd q v ξ → IsEquilibrium P m sd q' v' ξ' →
      q = q' ∧ v = v' ∧ ξ = ξ') := by sorry

end InvIntegration.Behavioral
