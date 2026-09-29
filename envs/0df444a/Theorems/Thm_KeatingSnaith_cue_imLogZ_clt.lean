-- Prove2me | Theorems.Thm_KeatingSnaith_cue_imLogZ_clt
-- name    : KeatingSnaith.cue_imLogZ_clt
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T13:08:31.873337+00:00
-- url     : https://prove2.me/theorems/cabed0fa-a748-4fd1-b6f5-27a2e6d0f410
-- title:
--   Central limit theorem for $\mathrm{Im}\log Z$
-- statement:
--   The **central limit theorem for the imaginary part of $\log Z$**.
--
--   For all real numbers $a$ and $b$,
--
--   $$
--   \lim_{N\to\infty}\;\Bigl\langle \mathbf{1}\Bigl[\frac{\operatorname{Im}\log Z}{\sqrt{\tfrac12\log N}}\in[a,b]\Bigr]\Bigr\rangle_{\mathrm{CUE}(N)} \;=\; \frac{1}{\sqrt{2\pi}}\int_a^b e^{-x^{2}/2}\,dx ,
--   $$
--
--   with $\operatorname{Im}\log Z=\sum_{n=1}^{N}(\theta_n-\pi)/2$ as fixed by the definition item.
--
--   Like the real part, the imaginary part has mean zero and variance $\tfrac12\log N+O(1)$, and standardising by $\sqrt{\tfrac12\log N}$ produces a standard Gaussian in the limit. Because $\operatorname{Im}\log Z$ measures, up to normalisation, the fluctuation of the number of eigenphases below a given point, this is simultaneously a central limit theorem for the eigenvalue counting function of $\mathrm{CUE}(N)$; the analogue for $\zeta$ is the Gaussian behaviour of $S(t)$, the argument of $\zeta$ on the critical line.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, pp. 50-53, §2.5 (value distribution of Im log Z), together with §2.3 eq. (2.3.8)

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- Central limit theorem for `Im log Z` (thesis §2.5). -/
theorem cue_imLogZ_clt (a c : ℝ) :
    Tendsto (fun N : ℕ => cueAverage N (fun θ =>
        Set.indicator (Set.Icc a c) (fun _ => (1 : ℝ)) (imLogZ N θ / cltScale N)))
      atTop (𝓝 (gaussianMass a c)) := by
  sorry

end KeatingSnaith
