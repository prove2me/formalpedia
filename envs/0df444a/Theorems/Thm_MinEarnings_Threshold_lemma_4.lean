-- Prove2me | Theorems.Thm_MinEarnings_Threshold_lemma_4
-- name    : MinEarnings.Threshold.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:12.442477+00:00
-- url     : https://prove2.me/theorems/cdfc62c8-961c-403b-93d1-ba4bfeaae893
-- title:
--   Lemma 4, p. 10 — the minimum earnings rule at price equal to wage
-- statement:
--   Consider a price-equals-wage policy at a period $t$ with $w_t\ge w^*$, where $D(w^*)=S(w^*)$. If positive earnings $z_t$ satisfy equilibrium, then the next wage meets the minimum earnings rule exactly when
--
--   $$w_{t+1}\ge\frac{M w_t}{H(R(w_t))},\qquad R(w)=wD(w).$$
--
--   This identity is the wage recurrence used in the stability threshold proof.
--
--   **Formalization Note** The theorem isolates the local equilibrium and wage hypotheses used by the printed lemma; a full sequence-level feasibility assumption is unnecessary for this equivalence. Positive earnings exclude zero utilization, and Lean's $t$ denotes the paper's period $t+1$.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), p. 10, Lemma 4; proof Online Appendix p. 3 (PDF 31)

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

namespace MinEarnings.Threshold

theorem lemma_4 (D S H : ℝ → ℝ) (pStar wStar M : ℝ)
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (hM : 0 < M) (w z : ℕ → ℝ) (t : ℕ)
    (hzt : 0 < z t ∧ z t = w t * util D S (w t) (z t))
    (hwt : wStar ≤ w t) :
    M / util D S (w t) (z t) ≤ w (t + 1) ↔
      M * w t / H (revenue D (w t)) ≤ w (t + 1) := by sorry

end MinEarnings.Threshold
