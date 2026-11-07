-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_11
-- name    : KramerSaglam.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:23.732193+00:00
-- url     : https://prove2.me/theorems/b4e25292-8a76-4f52-babf-3d19b502b193
-- title:
--   Lemma 3.11 — uniform estimates $B_N\le b_NR_N$, $R_N/(2e_N)<19/18$ and the bound on $C_N(u)$
-- statement:
--   For $N\ge2$ and $0\le u\le1$, with $x=1-u^{2N}$,
--   $$
--   B_N\le b_NR_N,\qquad\frac{R_N}{2e_N}<\frac{19}{18},\qquad\frac{C_N(u)}{2e_Nb_N}\ge 2x+\frac34x^2+\frac18x^3 .
--   $$
--   Here $e_N=\frac12\sum_{k=1}^N\frac1{2k-1}$ and $R_N=2T_N-1$.
--
--   These estimates, uniform in the coefficient index $N$, reduce the positivity of $c_N(u)$ for $N\ge2$ to that of the single function $J(w)$ (Lemma 3.12).
--
--   Differences from the source: none.
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.11 and the display before it (e_N, R_N, x), p.9

import Mathlib
import Definitions.Def_KramerSaglam_TailSeries

namespace KramerSaglam

/-- **Lemma 3.11.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.9. Here `x = 1 − u^{2N}`, from the display before the Lemma. -/
theorem lemma_3_11 (N : ℕ) (hN : 2 ≤ N) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    BB N ≤ b N * R N ∧ R N / (2 * e N) < 19 / 18 ∧
      CC N u / (2 * e N * b N) ≥
        2 * (1 - u ^ (2 * N)) + 3 / 4 * (1 - u ^ (2 * N)) ^ 2 + 1 / 8 * (1 - u ^ (2 * N)) ^ 3 := by sorry

end KramerSaglam
