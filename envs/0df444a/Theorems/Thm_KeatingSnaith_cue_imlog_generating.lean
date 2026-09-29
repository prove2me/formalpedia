-- Prove2me | Theorems.Thm_KeatingSnaith_cue_imlog_generating
-- name    : KeatingSnaith.cue_imlog_generating
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T12:50:52.614445+00:00
-- url     : https://prove2.me/theorems/8b9736f1-3e1d-4390-8bf6-eaf302467aea
-- title:
--   $\langle e^{is\,\mathrm{Im}\log Z}\rangle_{CUE} = \prod_{j=1}^{N}\frac{\Gamma(j)^2}{\Gamma(j+s/2)\Gamma(j-s/2)}$
-- statement:
--   This is the exact **characteristic function of $\operatorname{Im}\log Z$** over $\mathrm{CUE}(N)$.
--
--   Let $N\ge 1$ and let $s$ be real with $|s|<2$. Then
--
--   $$
--   \bigl\langle e^{\,i s \operatorname{Im}\log Z}\bigr\rangle_{\mathrm{CUE}(N)} \;=\; \prod_{j=1}^{N}\frac{\Gamma(j)^{2}}{\Gamma\!\left(j+\tfrac{s}{2}\right)\Gamma\!\left(j-\tfrac{s}{2}\right)} ,
--   $$
--
--   with $\operatorname{Im}\log Z=\sum_{n=1}^N(\theta_n-\pi)/2$ as fixed in the definition item. The left-hand side is a priori complex; the identity asserts in particular that it is real, as it must be since the distribution of $\operatorname{Im}\log Z$ is symmetric.
--
--   Written $L_N(s)$ in the source, this function plays for the imaginary part of $\log Z$ the role $M_N(s)$ plays for the real part: its logarithm generates the cumulants of $\operatorname{Im}\log Z$, and its large-$N$ behaviour after standardisation yields the Gaussian limit. The restriction $|s|<2$ is exactly the range in which the underlying Selberg integral converges.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, p. 34, eq. (2.1.18) with the validity condition |Re s| < 2 stated on p. 34

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- `⟨exp(i s Im log Z)⟩ = L̃_N(s)` (thesis eq. (2.1.18)). -/
theorem cue_imlog_generating (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hs : |s| < 2) :
    cueAverage N (fun θ => Complex.exp (s * imLogZ N θ * Complex.I))
      = ((∏ j ∈ Finset.range N,
            Real.Gamma (j + 1) ^ 2 /
              (Real.Gamma (j + 1 + s / 2) * Real.Gamma (j + 1 - s / 2)) : ℝ) : ℂ) := by
  sorry

end KeatingSnaith
