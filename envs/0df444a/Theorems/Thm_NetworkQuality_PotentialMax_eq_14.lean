-- Prove2me | Theorems.Thm_NetworkQuality_PotentialMax_eq_14
-- name    : NetworkQuality.PotentialMax.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:00.837539+00:00
-- url     : https://prove2.me/theorems/ce864946-f4be-44e8-ac01-8a29c56040e3
-- title:
--   (14), p. 15 — the firm's maximal profit at quality q under potential maximization is n·HM·(1/n)Σf(i,q) − c(q)
-- statement:
--   In the network market under the standing assumptions, fix a quality $q\ge 0$ with strong network effects, and let
--   $$p(q)=\Big(\frac1n\sum_{i=1}^n\frac1{v_i}\Big)^{-1}\frac1n\sum_{i=1}^n f(i,q)$$
--   be the threshold price of (12). Let $\Pi(p,q)$ be the firm's profit when stage 2 plays the potential maximizer ($np-c(q)$ if all consumers buying is a potential maximizer, $-c(q)$ otherwise). Then $p(q)\ge 0$,
--   $$\Pi(p(q),q)=n\Big(\frac1n\sum_{i=1}^n\frac1{v_i}\Big)^{-1}\frac1n\sum_{i=1}^n f(i,q)-c(q),$$
--   and $\Pi(p,q)$ is at most this value for every price $p\ge 0$.
--
--   So at each quality the firm optimally sets the highest price at which all consumers still buy under potential maximization, and (14) is its resulting profit as a function of quality; the firm's quality choice maximizes this reduced profit.
-- source:
--   Chan, Quality Strategies in Network Markets, SSRN 4203818 (version of April 2023), pp. 14–15, (14) and the sentence before (13)

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

namespace NetworkQuality.PotentialMax

open Market

theorem eq_14 {n : ℕ} (M : Market n) (hM : M.Standing) (q : ℝ) (hq : 0 ≤ q)
    (hs : M.StrongNE q) :
    0 ≤ ((1 / (n : ℝ)) * ∑ i : Fin n, 1 / M.v i)⁻¹ *
        ((1 / (n : ℝ)) * ∑ i : Fin n, M.f (i.val + 1) q) ∧
    M.profitPM (((1 / (n : ℝ)) * ∑ i : Fin n, 1 / M.v i)⁻¹ *
        ((1 / (n : ℝ)) * ∑ i : Fin n, M.f (i.val + 1) q)) q =
      (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, 1 / M.v i)⁻¹ *
        ((1 / (n : ℝ)) * ∑ i : Fin n, M.f (i.val + 1) q) - M.c q ∧
    ∀ p : ℝ, 0 ≤ p → M.profitPM p q ≤
      (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, 1 / M.v i)⁻¹ *
        ((1 / (n : ℝ)) * ∑ i : Fin n, M.f (i.val + 1) q) - M.c q := by sorry

end NetworkQuality.PotentialMax
