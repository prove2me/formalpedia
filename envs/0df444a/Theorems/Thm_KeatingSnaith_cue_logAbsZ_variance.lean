-- Prove2me | Theorems.Thm_KeatingSnaith_cue_logAbsZ_variance
-- name    : KeatingSnaith.cue_logAbsZ_variance
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T13:02:44.08716+00:00
-- url     : https://prove2.me/theorems/ca3b322f-0fb7-4c4e-a4c8-d89fe30e75c1
-- title:
--   The second cumulant $Q_2$ of $\log|Z|$
-- statement:
--   The **variance of $\log|Z|$** at finite matrix size, in closed form.
--
--   For every $N\ge1$,
--
--   $$
--   \bigl\langle (\log|Z|)^{2} \bigr\rangle_{\mathrm{CUE}(N)} \;=\; \frac12\Bigl(H_N \;+\; N\Bigl(\frac{\pi^{2}}{6}-\sum_{j=1}^{N}\frac{1}{j^{2}}\Bigr)\Bigr),
--   \qquad H_N=\sum_{j=1}^{N}\frac1j .
--   $$
--
--   Since the mean of $\log|Z|$ vanishes, the left-hand side is the variance, the second cumulant $Q_2$ of the source. The right-hand side is an elementary rewriting of the source's $\frac12\sum_{j=1}^N\psi^{(1)}(j) = \frac12[-\psi(1)+\psi(N+1)+N\psi^{(1)}(N+1)]$, obtained from $\psi(N+1)=-\gamma+H_N$ and $\psi^{(1)}(N+1)=\pi^2/6-\sum_{j\le N}j^{-2}$; stating it this way keeps the milestone free of any polygamma prerequisites. For $N=1$ it gives $\pi^2/12$, the classical value of $\frac{1}{2\pi}\int_0^{2\pi}\log^2|1-e^{i\theta}|\,d\theta$.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, pp. 37-38, eq. (2.2.15) Q2 = (1/2) sum_{j=1}^{N} psi'(j) and eq. (2.2.18) Q2 = (1/2)[-psi(1) + psi(N+1) + N psi'(N+1)]

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- The variance of `log |Z|` (thesis eq. (2.2.18)). -/
theorem cue_logAbsZ_variance (N : ℕ) (hN : 1 ≤ N) :
    cueAverage N (fun θ => logAbsZ N θ ^ 2)
      = (1 / 2) * ((∑ j ∈ Finset.range N, (1 : ℝ) / (j + 1)) +
          N * (Real.pi ^ 2 / 6 - ∑ j ∈ Finset.range N, (1 : ℝ) / (j + 1) ^ 2)) := by
  sorry

end KeatingSnaith
