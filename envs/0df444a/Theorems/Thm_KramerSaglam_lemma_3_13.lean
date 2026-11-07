-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_13
-- name    : KramerSaglam.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:13.775567+00:00
-- url     : https://prove2.me/theorems/40d12eda-d10c-4ea8-9dd2-678c04127846
-- title:
--   Lemma 3.13 — every coefficient $c_N(u)$ is positive
-- statement:
--   For every integer $N\ge1$ and $0<u\le1$,
--   $$
--   c_N(u)=C_N(u)+\frac{4G_N(u)}{u}-2B_N>0 .
--   $$
--
--   The $c_N(u)$ are the coefficients of the expansion in $r=\rho^2$ of the three-bit inequality (3.4), so their positivity proves Lemma 3.9.
--
--   Differences from the source: none.
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.13 and the definition of c_N before it, p.11

import Mathlib
import Definitions.Def_KramerSaglam_TailSeries

namespace KramerSaglam

/-- **Lemma 3.13.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.11: for every integer `N ≥ 1` and `0 < u ≤ 1`, `c_N(u) > 0`. -/
theorem lemma_3_13 (N : ℕ) (hN : 1 ≤ N) (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) : cN N u > 0 := by sorry

end KramerSaglam
