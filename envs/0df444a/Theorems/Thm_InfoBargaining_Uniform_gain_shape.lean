-- Prove2me | Theorems.Thm_InfoBargaining_Uniform_gain_shape
-- name    : InfoBargaining.Uniform.gain_shape
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:28.318179+00:00
-- url     : https://prove2.me/theorems/baef6013-72c8-4de6-8c4f-a7e2a057cb03
-- title:
--   Proof of Corollary 1, p. 30 — A(ᾱ, c) − A(α̲, c) is 0 outside ((1−ᾱ)/2, (1+ᾱ)/2), positive inside, rises then falls in c, peak (ᾱ − α̲)/8 at c = 1/2
-- statement:
--   Under the uniform prior, let $\Delta(c)=A(\bar\alpha,c)-A(\underline\alpha,c)$ be the gross surplus gain of maximal over minimal information. Then:
--
--   1. $\Delta(c)=0$ for $c\in(0,1)$ with $c\le(1-\bar\alpha)/2$ or $c\ge(1+\bar\alpha)/2$;
--   2. $\Delta(c)\ge 0$ for every $c\in(0,1)$;
--   3. $\Delta(c)>0$ for $c\in\big((1-\bar\alpha)/2,\,(1+\bar\alpha)/2\big)$;
--   4. $\Delta$ is strictly increasing on $[(1-\bar\alpha)/2,\,1/2]$ and strictly decreasing on $[1/2,\,(1+\bar\alpha)/2]$;
--   5. its peak value is
--   $$\Delta(1/2)=\frac{\bar\alpha-\underline\alpha}{8}.$$
--
--   The marginal value of information is thus largest when the seller's cost equals the prior mean $\hat u=1/2$ and vanishes when the cost is extreme. This inverted-U shape produces the two cost thresholds $c_l\le\hat u\le c_h$ of Corollary 1 (ii).
--
--   **Formalization Note** Two printed slips are corrected. The page says the inequality $A(\bar\alpha,c)\ge A(\underline\alpha,c)$ is strict on the closed interval $[(1-\bar\alpha)/2,(1+\bar\alpha)/2]$, but by item 1 the gain is $0$ at its endpoints, so item 3 uses the open interval. The page gives the peak value as $\theta_b(\bar\alpha-\underline\alpha)/8$, but $A(\alpha,1/2)=\alpha/8$, so the peak of $\Delta$ is $(\bar\alpha-\underline\alpha)/8$ (the factor $\theta_b$ belongs to $U_b$).
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 30, Appendix, proof of Corollary 1, second and third paragraphs

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

namespace InfoBargaining.Uniform

theorem gain_shape (M : Model) :
    (∀ c ∈ Set.Ioo (0:ℝ) 1, (c ≤ (1 - M.αhi) / 2 ∨ (1 + M.αhi) / 2 ≤ c) → M.gain c = 0) ∧
    (∀ c ∈ Set.Ioo (0:ℝ) 1, 0 ≤ M.gain c) ∧
    (∀ c ∈ Set.Ioo ((1 - M.αhi) / 2) ((1 + M.αhi) / 2), 0 < M.gain c) ∧
    StrictMonoOn M.gain (Set.Icc ((1 - M.αhi) / 2) (1 / 2)) ∧
    StrictAntiOn M.gain (Set.Icc (1 / 2) ((1 + M.αhi) / 2)) ∧
    M.gain (1 / 2) = (M.αhi - M.αlo) / 8 := by sorry

end InfoBargaining.Uniform
