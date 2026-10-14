-- Prove2me | Theorems.Thm_LindelofHypothesis_ingham_density_estimate
-- name    : LindelofHypothesis.ingham_density_estimate
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:52:13.9421+00:00
-- url     : https://prove2.me/theorems/4691a87d-6523-4153-8555-26fb32d58ac0
-- title:
--   Ingham's zero-density estimate $N(\sigma,T)\ll T^{\frac{3}{2-\sigma}(1-\sigma)+\varepsilon}$
-- statement:
--   Let $N(\sigma,T)$ be the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho\ge\sigma$ and $|\operatorname{Im}\rho|\le T$, counted with multiplicity. For every $\sigma\in[\tfrac12,1]$ and every $\varepsilon>0$,
--   $$N(\sigma,T)\ll T^{A_I(\sigma)(1-\sigma)+\varepsilon},\qquad A_I(\sigma)=\frac{3}{2-\sigma}.$$
--
--   This is Ingham's 1940 zero-density estimate, unconditional.
--
--   **Formalization Note** Stated in the form $N(\sigma,T)\ll T^{A(\sigma)(1-\sigma)+\varepsilon}$ of the source, on the range $\tfrac12\le\sigma\le1$ of Ingham's theorem. Counts are elements of $\mathbb N\cup\{\infty\}$ (cast to $[0,\infty]$), so the bound also asserts that the count is finite.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The density hypothesis", sentence "Ingham showed that A_I(σ) = 3/(2 − σ) in 1940".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem ingham_density_estimate (σ : ℝ) (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (3 / (2 - σ) * (1 - σ) + ε)) := by sorry

end LindelofHypothesis
