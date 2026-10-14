-- Prove2me | Theorems.Thm_LindelofHypothesis_density_hypothesis_of_lindelof
-- name    : LindelofHypothesis.density_hypothesis_of_lindelof
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:51:22.486035+00:00
-- url     : https://prove2.me/theorems/8c7eeb14-1f3c-439c-a1c9-ce0f5d5c278e
-- title:
--   Under Lindelöf, the density hypothesis $N(\sigma,T)\ll T^{2(1-\sigma)+\varepsilon}$ holds
-- statement:
--   Let $N(\sigma,T)$ be the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho\ge\sigma$ and $|\operatorname{Im}\rho|\le T$, counted with multiplicity. Assume the Lindelöf hypothesis. Then for every $\sigma\in[\tfrac12,1]$ and every $\varepsilon>0$,
--   $$N(\sigma,T)\ll T^{2(1-\sigma)+\varepsilon}\qquad(T\to\infty).$$
--
--   This is the **density hypothesis**, which the source records as following from the Lindelöf hypothesis.
--
--   **Formalization Note** `RiemannVonMangoldt.LindelofHypothesis` is the published definition: for every $\varepsilon>0$, $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$. The source writes $N(\sigma,T)\le N^{2(1-\sigma)+\varepsilon}$; the base $N$ is read as $T$, the standard form of the density hypothesis, and $\le$ as $\ll$ (an implied constant, $T$ large). The range $\tfrac12\le\sigma\le1$ is the standard range of the density hypothesis. Counts are elements of $\mathbb N\cup\{\infty\}$ (cast to $[0,\infty]$), so the bound also asserts that the count is finite.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The density hypothesis", first sentence ("... and it would follow from the Lindelöf hypothesis").

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem density_hypothesis_of_lindelof (hL : RiemannVonMangoldt.LindelofHypothesis)
    (σ : ℝ) (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (2 * (1 - σ) + ε)) := by sorry

end LindelofHypothesis
