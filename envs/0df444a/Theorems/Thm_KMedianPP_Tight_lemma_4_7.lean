-- Prove2me | Theorems.Thm_KMedianPP_Tight_lemma_4_7
-- name    : KMedianPP.Tight.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:02:43.961829+00:00
-- url     : https://prove2.me/theorems/ea400e80-b490-4ca9-b4ee-70ce1532e872
-- title:
--   Lemma 4.7 — forcing a hit in the equal-mass process: $p_{r-1,s-1}\le p_{r,s}$ and $R_{r-1,s-1}-mp_{r-1,s-1}\le R_{r,s}-mp_{r,s}$
-- statement:
--   For any weight $\Gamma>0$ and integer $\Delta\ge0$, let $r,s\ge1$ and $m=r+\Delta-s\ge0$. Then, for the equal-mass process with permanent weight $\Gamma$ and $p_{r,s}=\mathbb E[J/(\Delta+J)]$,
--   $$p_{r-1,s-1}\le p_{r,s}\qquad\text{and}\qquad R_{r-1,s-1}-m\,p_{r-1,s-1}\le R_{r,s}-m\,p_{r,s}.$$
--
--   Differences from the source:
--   - encoding: integers Δ ≥ 0, r, s ≥ 1, m = r + Δ − s ≥ 0 → `Δ r s : ℕ`, `1 ≤ r`, `1 ≤ s`, `s ≤ r + Δ`, and m written as the real `(r : ℝ) + Δ − s`; reason: same range; no truncated subtraction
--   - encoding: R_{r,s} = E[J], p_{r,s} = E[J/(Δ + J)] with footnote 5 at Δ = J = 0 → `R Γ r s`, `p Γ Δ r s`: sums over j ≤ r against the law `jLaw Γ r s` of J, defined by first-step conditioning; reason: the law of J of the same Markov chain
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 22 (PDF 24), Lemma 4.7

import Mathlib
import Definitions.Def_KMedianPP_Tight_EqualMass

set_option autoImplicit false

namespace KMedianPP.Tight

/-- Lemma 4.7 (p. 22): for any weight `Γ > 0`, let `r, s ≥ 1` and `m = r + Δ - s ≥ 0`. Then
`p_{r-1,s-1} ≤ p_{r,s}` and `R_{r-1,s-1} - m p_{r-1,s-1} ≤ R_{r,s} - m p_{r,s}`. -/
theorem lemma_4_7 (Γ : ℝ) (hΓ : 0 < Γ) (Δ r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hm : s ≤ r + Δ) :
    p Γ Δ (r - 1) (s - 1) ≤ p Γ Δ r s ∧
    R Γ (r - 1) (s - 1) - ((r : ℝ) + Δ - s) * p Γ Δ (r - 1) (s - 1) ≤
      R Γ r s - ((r : ℝ) + Δ - s) * p Γ Δ r s := by sorry

end KMedianPP.Tight
