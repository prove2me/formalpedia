-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_eta_star_limit
-- name    : MarketplaceLeakage.Communication.eta_star_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:27.627376+00:00
-- url     : https://prove2.me/theorems/e51e125e-feef-49a1-b18d-d8d30ffaf49e
-- title:
--   §8.4, p. 38 — lim_{q→1} η* = 1
-- statement:
--   Let $c<v$ and let
--   $$\eta^*(q)=\frac{qv(2-q)-c-q\sqrt{(1-q)\,v\,(v-c)}}{qv\,\bigl(3(1-q)+q^2\bigr)-c}.$$
--   Then
--   $$\lim_{q\to1^-}\eta^*(q)=1 .$$
--
--   Since the ban profit is at least $\Pi_H(\eta^*)$ for every $\eta$, this limit is what makes banning communication optimal for every $\eta$ once the prior probability $q$ of a high valuation is close to one.
--
--   **Formalization Note.** The limit is taken from the left, $q\uparrow 1$, since $q\in(0,1)$ in the model.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 38, §8.4, Proof of Proposition 3, "Since lim_{q→1} η* = 1"

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

namespace MarketplaceLeakage.Communication

theorem eta_star_limit (v c : ℝ) (hvc : c < v) :
    Filter.Tendsto (etaStar v c) (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by sorry

end MarketplaceLeakage.Communication
