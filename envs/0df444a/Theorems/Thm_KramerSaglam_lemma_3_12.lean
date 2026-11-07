-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_12
-- name    : KramerSaglam.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:34.311544+00:00
-- url     : https://prove2.me/theorems/8af3220a-8181-4c2d-b3e5-fc98bf5474fa
-- title:
--   Lemma 3.12 — $J(w)>0$ on $(0,1)$
-- statement:
--   For $0<w<1$,
--   $$
--   J(w)=\frac{55}{72}-\frac{31w^4}{8}+\frac{9w^8}{8}-\frac{w^{12}}{8}+\frac{38\,s_2(w)}{w}>0,
--   $$
--   where $s_2(w)=\sum_{k>2}w^{2k}/(2k(2k-1))$.
--
--   Every coefficient $c_N(u)$ of index $N\ge2$ is bounded below by a positive multiple of $J(u^{N/2})$, so this is the last analytic input of the proof.
--
--   Differences from the source: none.
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.12 and the definition of J before it, p.10

import Mathlib
import Definitions.Def_KramerSaglam_TailSeries

namespace KramerSaglam

/-- **Lemma 3.12.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.10: for `0 < w < 1`, `J(w) > 0`. -/
theorem lemma_3_12 (w : ℝ) (h0 : 0 < w) (h1 : w < 1) : JJ w > 0 := by sorry

end KramerSaglam
