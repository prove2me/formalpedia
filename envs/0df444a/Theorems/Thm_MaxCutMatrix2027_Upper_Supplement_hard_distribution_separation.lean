-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_hard_distribution_separation
-- name    : MaxCutMatrix2027.Upper.Supplement.hard_distribution_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:08:40.633855+00:00
-- url     : https://prove2.me/theorems/6c5f3d36-2023-41ac-888a-7a029f47b7ce
-- title:
--   Lemma 5.2 — Hard-distribution MAX-CUT separation
-- statement:
--   Let $0<\varepsilon\le 1/160$, let $n\ge\lceil 1/\varepsilon^2\rceil$ be an integer, put $\rho=40\varepsilon$, and let $D_0,D_1$ be the no and yes laws of Definition 5.1. Define
--   $$u_*=\frac{n^2}{8}+n^{3/2},\qquad l_*=\Bigl(\frac12+20\varepsilon\Bigr)\frac{n^2-9n}{4}-n.$$
--   Then
--   $$l_*-u_*>2\varepsilon n^2,\qquad \Pr_{G\sim D_0}\bigl(\mathrm{MAXCUT}(G)>u_*\bigr)<0.001,\qquad \Pr_{G\sim D_1}\bigl(\mathrm{MAXCUT}(G)<l_*\bigr)<0.023 .$$
--
--   The two thresholds separate the MAX-CUT values of the two hard laws by more than twice the allowed error, so an accurate tester distinguishes the laws; this is used by both lower bounds.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: signs and edge indicators in {−1,1} (Y = −1 an edge) → Booleans (true ↦ sign 1; answer true = edge); reason: bijective relabeling; every quantity is transported unchanged
--   - encoding: the distributions D0, D1 and D1^joint of Definition 5.1 → explicit finite mass functions noLaw, yesLaw = ∑_σ yesJoint with yesJoint(σ,G) = 2^{-n} ∏_{u<v} Pr(Y_uv | σ); reason: these are exactly the product laws of Definition 5.1 and Eq. (35)
--   - encoding: n^{3/2} → n·√n; reason: equal for every n ≥ 0
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 5.2, p.28 (PDF p.28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_QueryModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper.Supplement

/-- Lemma 5.2, p.28, for the hard laws of Definition 5.1 with `ρ = 40ε`. -/
theorem hard_distribution_separation (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 160)
    (n : ℕ) (hn : ⌈1 / ε ^ 2⌉₊ ≤ n) :
    let u : ℝ := (n : ℝ) ^ 2 / 8 + (n : ℝ) * Real.sqrt n
    let l : ℝ := (1 / 2 + 20 * ε) * ((n : ℝ) ^ 2 - 9 * n) / 4 - n
    l - u > 2 * ε * (n : ℝ) ^ 2 ∧
    lawProb (fun G : SimpleGraph (Fin n) => noLaw G) (fun G => u < maxCutR G) < 0.001 ∧
    lawProb (fun G : SimpleGraph (Fin n) => yesLaw (40 * ε) G) (fun G => maxCutR G < l) < 0.023 := by sorry

end MaxCutMatrix2027.Upper.Supplement
