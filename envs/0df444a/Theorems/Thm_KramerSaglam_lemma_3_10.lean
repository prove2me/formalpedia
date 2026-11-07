-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_10
-- name    : KramerSaglam.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:12.601207+00:00
-- url     : https://prove2.me/theorems/8b735eb2-9f05-45a3-a7ea-3596d9e71ebc
-- title:
--   Lemma 3.10 — two comparisons of the divergence tails, (3.5) and (3.6)
-- statement:
--   For $0<u<1$ and $N\ge1$,
--   $$
--   G_N(u)\ge B_N\,\frac{s_N(u)}{b_N}.\tag{3.5}
--   $$
--   For $N\ge2$, also
--   $$
--   \frac{s_N(u)}{u\,b_N}\ge\frac{s_2(u^{N/2})}{u^{N/2}\,b_2}.\tag{3.6}
--   $$
--   Here $b_N,s_N,B_N,G_N$ are the divergence tails and their convolutions of §3.3 (with $b_0=1$).
--
--   These reduce the coefficient $c_N(u)$ of every index $N\ge2$ to a function of the single variable $w=u^{N/2}$.
--
--   **Formalization Note** $u^{N/2}$ is a real power, since $N/2$ may be a half-integer.
--
--   Differences from the source: none.
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.10, displays (3.5) and (3.6), p.8

import Mathlib
import Definitions.Def_KramerSaglam_TailSeries

namespace KramerSaglam

/-- **Lemma 3.10.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.8, displays (3.5) and (3.6). `u^{N/2}` is a real power, since `N/2` can be a half-integer. -/
theorem lemma_3_10 (u : ℝ) (h0 : 0 < u) (h1 : u < 1) :
    (∀ N : ℕ, 1 ≤ N → G N u ≥ BB N * (s N u / b N)) ∧
    (∀ N : ℕ, 2 ≤ N →
      s N u / (u * b N) ≥ s 2 (u ^ ((N : ℝ) / 2)) / (u ^ ((N : ℝ) / 2) * b 2)) := by sorry

end KramerSaglam
