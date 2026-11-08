-- Prove2me | Theorems.Thm_KhintchineTwoRegime_lemma_1
-- name    : KhintchineTwoRegime.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:54.040195+00:00
-- url     : https://prove2.me/theorems/f8eed33f-85d1-4dc0-9428-3cb37e51f047
-- title:
--   Lemma 1 — sharper Wallis-ratio estimate $F(s)\ge C(1+\frac1{2s}+\frac1{8s(s+1/2)})^{-1/2}$
-- statement:
--   Let $F$ be Haagerup's function (8) and $C=\sqrt{2/\pi}$. For every $s>0$,
--   $$
--   F(s)\ \ge\ C\Bigl(1+\frac1{2s}+\frac1{8s(s+1/2)}\Bigr)^{-1/2}.
--   $$
--   Equivalently, with $r(u)=\sqrt{(8+4u^2)/(8+8u^2+3u^4)}$,
--   $$
--   F(u^{-2})\ \ge\ C\,r(u)\qquad(u>0).
--   $$
--   Both forms are stated. The estimate turns Haagerup's inequality (9) into the explicit coefficient bound $H$ of Lemma 2.
--
--   Differences from the source:
--   - encoding: (1 + 1/(2s) + 1/(8s(s + 1/2)))^{−1/2} and F(u^{−2}) → 1/√(1 + 1/(2s) + 1/(8s(s + 1/2))) and F((u²)⁻¹); reason: the base is positive for s > 0, so X^{−1/2} = 1/√X; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 1, eq. (10), p.6

import Mathlib
import Definitions.Def_KhintchineTwoRegime_haagerupF
import Definitions.Def_KhintchineTwoRegime_Cconst
import Definitions.Def_KhintchineTwoRegime_rFun

namespace KhintchineTwoRegime

/-- Lemma 1 (A sharper Wallis-ratio estimate) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (10), p.6): for every `s > 0`,
`F(s) ≥ C (1 + 1/(2s) + 1/(8s(s + 1/2)))^{−1/2}`; equivalently `F(u^{−2}) ≥ C r(u)` for
`u > 0`.

**Formalization Note** `X^{−1/2}` is written `1/√X` (the base is positive for `s > 0`), and
`u^{−2}` is `(u²)⁻¹`. Both printed forms are stated. -/
theorem lemma_1 :
    (∀ s : ℝ, 0 < s →
      Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2))) ≤ haagerupF s) ∧
    (∀ u : ℝ, 0 < u → Cconst * rFun u ≤ haagerupF ((u ^ 2)⁻¹)) := by sorry

end KhintchineTwoRegime
