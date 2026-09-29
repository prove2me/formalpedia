-- Prove2me | Theorems.Thm_KeatingSnaith_cue_logAbsZ_clt
-- name    : KeatingSnaith.cue_logAbsZ_clt
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T13:07:53.868696+00:00
-- url     : https://prove2.me/theorems/a3350a46-11b6-497c-9155-6eacf4109aaf
-- title:
--   Central limit theorem for $\log|Z|$
-- statement:
--   The **central limit theorem for the real part of $\log Z$**, the random-matrix analogue of Selberg's theorem for $\log|\zeta(1/2+it)|$.
--
--   For all real numbers $a$ and $b$,
--
--   $$
--   \lim_{N\to\infty}\;\Bigl\langle \mathbf{1}\Bigl[\frac{\log|Z|}{\sqrt{\tfrac12\log N}}\in[a,b]\Bigr]\Bigr\rangle_{\mathrm{CUE}(N)} \;=\; \frac{1}{\sqrt{2\pi}}\int_a^b e^{-x^{2}/2}\,dx .
--   $$
--
--   The left-hand side is the CUE probability that the standardised variable lies in $[a,b]$; the right-hand side is the standard Gaussian mass of $[a,b]$. Since $\log|Z|$ has mean zero and variance $\tfrac12\log N+O(1)$, the scaling by $\sqrt{\tfrac12\log N}$ is the correct standardisation, and the theorem says that no other feature of the distribution survives the limit.
--
--   For $\zeta$ the corresponding statement is Selberg's central limit theorem with $\log\log T$ in place of $\log N$; the agreement of the two is the basis of the value-distribution part of the Keating–Snaith correspondence.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, pp. 43-45, §2.3, eq. (2.3.8) and the standardisation (2.3.10)-(2.3.11)

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- Central limit theorem for `log |Z|` (thesis §2.3, eq. (2.3.8)). -/
theorem cue_logAbsZ_clt (a c : ℝ) :
    Tendsto (fun N : ℕ => cueAverage N (fun θ =>
        Set.indicator (Set.Icc a c) (fun _ => (1 : ℝ)) (logAbsZ N θ / cltScale N)))
      atTop (𝓝 (gaussianMass a c)) := by
  sorry

end KeatingSnaith
