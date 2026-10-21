-- Prove2me | Theorems.Thm_G2GImport_Sourcing_D2_root
-- name    : G2GImport.Sourcing.D2_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:35.380989+00:00
-- url     : https://prove2.me/theorems/97cafdd2-54b9-4e5b-8f1c-89ea09077c9b
-- title:
--   Proposition 3 proof: quadratic payoff gap and positive crossing
-- statement:
--   For $0<\gamma<1$ and $0<c<1-\gamma$, let $D_2(l)$ be the quadratic polynomial printed in the proof of Proposition 3, and let $U_B^{a*}(l)$ and $U_B^{f*}(l)$ be its two buyer-payoff formulas. For every real $l>0$,
--   $$U_B^{f*}(l)-U_B^{a*}(l)=\frac{D_2(l)}{3(1-\gamma)l^2}.$$
--   The coefficient of $l^2$ is positive, while $D_2(0)=-(1-\sqrt c)^3(\gamma-1)^2<0$. Thus $D_2$ has a unique positive root $\underline l$, and $D_2(l)>0$ for every $l>\underline l$.
--
--   The root supplies the supplier-count threshold beyond which the forward regime gives the buyer more utility.
--
--   **Formalization Note** The polynomial and closed payoffs are defined on real $l$, extending the supplier count from positive integers as the paper does.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF pp. 14–15, proof of Proposition 3, D₂ identity and positive-root argument

import Mathlib
import Definitions.Def_G2GImport_Sourcing_ClosedForms

namespace G2GImport.Sourcing

/-- The quadratic payoff-gap identity and its unique positive crossing, from the
proof of Proposition 3. -/
theorem D2_root (P : Params) (hS : P.Standing) :
    (∀ l : ℝ, 0 < l →
      fwdBuyerClosed P l - adHocBuyerClosed P l =
        D₂ P l / (3 * (1 - P.γ) * l ^ 2)) ∧
    0 < (2 * (1 - P.γ) + (3 * P.γ - 2) *
      Real.sqrt (1 / (1 - P.γ))) * P.c ^ ((3 : ℝ) / 2) ∧
    D₂ P 0 = -(1 - Real.sqrt P.c) ^ 3 * (P.γ - 1) ^ 2 ∧
    D₂ P 0 < 0 ∧
    ∃ lowerL : ℝ, 0 < lowerL ∧ D₂ P lowerL = 0 ∧
      (∀ l : ℝ, lowerL < l → 0 < D₂ P l) ∧
      (∀ l : ℝ, 0 < l → D₂ P l = 0 → l = lowerL) := by sorry

end G2GImport.Sourcing
