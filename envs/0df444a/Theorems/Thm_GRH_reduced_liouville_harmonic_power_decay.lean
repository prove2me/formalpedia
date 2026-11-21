-- Prove2me | Theorems.Thm_GRH_reduced_liouville_harmonic_power_decay
-- name    : GRH.reduced_liouville_harmonic_power_decay
-- status  : Open
-- author  : @pragyan
-- created : 2026-11-21T01:12:56.499549+00:00
-- url     : https://prove2.me/theorems/005c4a44-c584-4977-a8a6-0b3e4ee0fd30
-- title:
--   Harmonic Liouville cancellation away from the modulus
-- statement:
--   For a fixed positive integer $q$, put
--   $$H_q(U)=\sum_{\substack{1\le d\le U\\(d,q)=1}}\frac{\lambda(d)}d.$$
--   For every $1/2<\sigma<1$, the proposed open estimate asserts the existence of a constant $K=K(q,\sigma)\ge0$ such that
--   $$|H_q(U)|\le K(U+1)^{\sigma-1}\qquad(U\ge0).$$
--   This is a conjectural harmonic Liouville cancellation input. It concerns only coprimality with the modulus, rather than individual residue classes, and isolates the scalar main term in the centered squarefree bilinear decomposition. The sources define the arithmetic functions and their Euler products; they do not establish this conjectural decay estimate.
-- source:
--   Proposed open principal-factor input for the main-term decomposition of https://prove2.me/theorems/dd1bd87e-604f-4753-a99c-ded025ae6c8e. Definitions: NIST DLMF §27.2(i), equations (27.2.12)–(27.2.13), https://dlmf.nist.gov/27.2#E13 ; Euler products: §27.4, equations (27.4.1) and (27.4.5), https://dlmf.nist.gov/27.4 . The power decay is conjectural, not a theorem claimed from these references.

import Definitions.Def_GRH_SquarefreeBilinear

theorem GRH.reduced_liouville_harmonic_power_decay
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ,
      |GRH.reducedLiouvilleHarmonic q U| ≤ K * ((U : ℝ) + 1) ^ (σ - 1) := by sorry
