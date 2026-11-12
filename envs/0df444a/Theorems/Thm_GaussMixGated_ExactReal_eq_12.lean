-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_eq_12
-- name    : GaussMixGated.ExactReal.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:34.719217+00:00
-- url     : https://prove2.me/theorems/5ea60f0d-5162-4f8d-8158-8bb065cd4d54
-- title:
--   §2.2, display (12) — the omitted-mass recursion
-- statement:
--   Let $d\ge1$, $0<\varepsilon,\delta<1/4$, $C_{\mathrm{cov}}\ge1$, and let $A_*$, $J$ and $\beta$ be as in (7)–(8). Let $b_0,b_1,\dots$ be nonnegative reals with $b_0\le\beta$ such that, for every $j<J$ with $b_j\le1/2$,
--
--   $$b_{j+1}\le b_j+(1-b_j)\{3\beta+C_{\mathrm{cov}}(2b_j+\beta)\}.$$
--
--   Then for every $0\le j\le J$,
--
--   $$b_j\le3A_*^j\beta\le\varepsilon^2/1000,\qquad(12)$$
--
--   and in particular $b_j\le1/2$. In the paper $b_j$ is the latent mass outside the stage-$j$ cover, and the recursion is (6) with $e=2b_j+\beta$ from (4) with $a=\beta$. This display keeps the omitted mass small across all $J+1$ stages.
--
--   Differences from the source:
--   - generalization: b_j the omitted masses of the algorithm on the success events, C_cov the constant of Theorem 2.3 → any nonnegative sequence with b₀ ≤ β obeying the recursion at stages with b_j ≤ 1/2, any C_cov ≥ 1; reason: the display is an arithmetic consequence of these facts; it specializes to the source's b_j
--   - reading: 'This verifies the hypothesis b_j ≤ 1/2 at every stage' → b_j ≤ 1/2 stated as a third conclusion; reason: it is the purpose of the display
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 8 (printed p. 6), §2.2, display (12); recursion on PDF p. 7

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Schedule

namespace GaussMixGated.ExactReal

/-- §2.2, display (12) (Zheng–Xie–He, STOC 2027 #36, PDF pp. 7–8): the omitted-mass recursion
`b_{j+1} ≤ b_j + (1 − b_j){3β + C_cov(2b_j + β)}` (valid at stages with `b_j ≤ 1/2`), started from
`b₀ ≤ β`, gives `b_j ≤ 3 A*^j β ≤ ε²/1000` for `0 ≤ j ≤ J`; in particular `b_j ≤ 1/2`. -/
theorem eq_12 (d : ℕ) (hd : 1 ≤ d) (ε δ Ccov : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 4)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hC : 1 ≤ Ccov) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hb0 : b 0 ≤ betaSched d ε δ Ccov)
    (hrec : ∀ j < Jsched d δ, b j ≤ 1 / 2 →
      b (j + 1) ≤ b j + (1 - b j) *
        (3 * betaSched d ε δ Ccov + Ccov * (2 * b j + betaSched d ε δ Ccov))) :
    ∀ j ≤ Jsched d δ,
      b j ≤ 3 * Astar Ccov ^ j * betaSched d ε δ Ccov ∧
      3 * Astar Ccov ^ j * betaSched d ε δ Ccov ≤ ε ^ 2 / 1000 ∧
      b j ≤ 1 / 2 := by sorry

end GaussMixGated.ExactReal
