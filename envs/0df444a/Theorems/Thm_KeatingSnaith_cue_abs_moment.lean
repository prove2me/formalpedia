-- Prove2me | Theorems.Thm_KeatingSnaith_cue_abs_moment
-- name    : KeatingSnaith.cue_abs_moment
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T12:13:44.658052+00:00
-- url     : https://prove2.me/theorems/8f99f953-ed68-4ce0-9c39-6a75393c0955
-- title:
--   $\langle|Z|^s\rangle_{CUE} = \prod_{j=1}^{N}\frac{\Gamma(j)\Gamma(s+j)}{\Gamma(j+s/2)^2}$
-- statement:
--   This is the central exact computation of the chapter: the **$s$-th moment of $|Z|$** over $\mathrm{CUE}(N)$.
--
--   Let $N\ge 1$ and let $s$ be a real number with $s>-1$. Then
--
--   $$
--   \bigl\langle |Z|^{s}\bigr\rangle_{\mathrm{CUE}(N)} \;=\; \prod_{j=1}^{N}\frac{\Gamma(j)\,\Gamma(s+j)}{\Gamma\!\left(j+\tfrac{s}{2}\right)^{2}} ,
--   $$
--
--   where $Z=\prod_{n=1}^N(1-e^{i\theta_n})$ and the average is the CUE average of the mission's definition item. In the Lean statement the product is written over $j=0,\dots,N-1$ with every argument shifted by one, which is the same product.
--
--   The right-hand side, written $M_N(s)$ in the source, is an entirely explicit function of $s$ and $N$ with no asymptotics involved. It is at once the moment of $|Z|$ and the moment generating function of $\log|Z|$: differentiating at $s=0$ produces the moments of $\log|Z|$, and its logarithm generates the cumulants. Transferred to the Riemann zeta function, it is the origin of the Keating–Snaith conjecture for the moments of $\zeta(1/2+it)$.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, p. 31, eq. (2.1.9), valid for Re s > -1

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- `⟨|Z|^s⟩ = M_N(s)` (thesis eq. (2.1.9)). -/
theorem cue_abs_moment (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hs : -1 < s) :
    cueAverage N (fun θ => ‖charPoly N θ‖ ^ s)
      = ∏ j ∈ Finset.range N,
          Real.Gamma (j + 1) * Real.Gamma (s + j + 1) / Real.Gamma (j + 1 + s / 2) ^ 2 := by
  sorry

end KeatingSnaith
