-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_lemma_3_6
-- name    : LiqProvision.Oligopoly.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:38.595299+00:00
-- url     : https://prove2.me/theorems/f0ed64ff-1b7c-4a46-85ce-9b05d9963910
-- title:
--   Lemma 3.6, p. 10 — the marginal prices of a symmetric Nash equilibrium solve the ODE (3.8)
-- statement:
--   Assume the standing assumptions ($K\ge2$, $\gamma_c>0$, $\gamma_d\ge0$, positive probability densities) and Assumption 2.1. If $P_*$ is a symmetric Nash equilibrium for $K$ dealers, then its marginal prices $P'=P_*'$ satisfy, for $n<0$ and $n>0$ respectively,
--   $$P''(n)=\frac{(K-1)\gamma_c\big(\gamma_dn-P'(n)+g(P'(n)+\gamma_cKn)\big)}{\frac{F}{f}(P'(n)+\gamma_cKn)-\big(\gamma_dn-P'(n)+g(P'(n)+\gamma_cKn)\big)},\qquad
--   P''(n)=\frac{(K-1)\gamma_c\big(\gamma_dn-P'(n)+g(P'(n)+\gamma_cKn)\big)}{-\frac{\bar F}{f}(P'(n)+\gamma_cKn)-\big(\gamma_dn-P'(n)+g(P'(n)+\gamma_cKn)\big)},$$
--   and the denominators never vanish.
--
--   This is the necessity half of the characterization: any equilibrium is pinned down by (3.8).
--
--   **Formalization Note.** The model objects are those of `LiqProvision.Oligopoly.Model`. The conclusion is the predicate (3.8) applied to the derivative $P_*'$ of $P_*$, including the nonvanishing of the denominators.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 10, Lemma 3.6, (3.8); proof pp. 21–22

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
theorem lemma_3_6 (M : Params) (hS : M.Standing) (h21 : M.Assumption21) (P : ℝ → ℝ)
    (hP : IsSymNE M P) : ODEHolds M (deriv P) := by sorry
end LiqProvision.Oligopoly
