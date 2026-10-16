-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_lemma1_benchmark
-- name    : NewsBundling.Unilateral.lemma1_benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:46.391996+00:00
-- url     : https://prove2.me/theorems/cc2c770b-6f34-4141-90d9-a086802f93ff
-- title:
--   Lemma 1, p. 10 — benchmark quality and publisher profit
-- statement:
--   Consider the same sequential game with content bundling unavailable, $\Lambda=0$. Let $\beta>0$ be revenue per unit of direct newspaper time and let $c>2\beta$ be the quality-cost parameter. An equilibrium exists, and every benchmark equilibrium has news quality $\hat q$ and publisher profit $\hat\pi_1$ given by
--
--   $$\hat q=\frac{\beta}{c},\qquad \hat\pi_1=\frac{\beta^2}{2c}.$$
--
--   This identifies the comparison point for Proposition 1.
--
--   **Formalization Note** The platform and indirect-revenue parameters $\phi_0,\phi_1$ are arbitrary because the platform's news share is forced to zero. The existence clause excludes a vacuous reading of “every equilibrium.”
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 10, Lemma 1

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Lemma 1, p. 10: benchmark equilibrium quality and profit. -/
theorem lemma1_benchmark (β φ0 φ1 c : ℝ) (hβ : 0 < β) (hc : 2 * β < c) :
    (∃ σ, IsSPE β φ0 φ1 c 0 σ) ∧
      ∀ σ, IsSPE β φ0 φ1 c 0 σ →
        σ.quality = β / c ∧ eqProfit β φ1 c σ = β ^ 2 / (2 * c) := by sorry

end NewsBundling.Unilateral
