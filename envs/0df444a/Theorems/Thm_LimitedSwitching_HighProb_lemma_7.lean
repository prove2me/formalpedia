-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_lemma_7
-- name    : LimitedSwitching.HighProb.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:00.354193+00:00
-- url     : https://prove2.me/theorems/8d9cd3c4-521e-4e12-a3f4-e8584a697d8b
-- title:
--   Lemma 7, p. 13 (FPL* with perturbation −R/ε; sign corrected) — E[Switches_τ(FPL*_ε)] ≤ (ετ + 2 log n)/(1 − ε)
-- statement:
--   Let $n\ge1$ and $0<\varepsilon<1$, and let $(\ell_t)$ be any loss sequence with values in $[0,1]$, fixed in advance. Run FPL$^*_\varepsilon$: draw $R(1),\dots,R(n)$ i.i.d. standard exponential, and at each round $t$ play the action minimising $-R(i)/\varepsilon+\sum_{s=1}^{t-1}\ell_s(i)$. Then for every horizon $\tau\in\mathbb N$ the expected number of switches satisfies
--
--   $$\mathbb E\big[\mathrm{Switches}_\tau(\mathrm{FPL}^*_\varepsilon)\big]\le\frac{1}{1-\varepsilon}\,(\varepsilon\tau+2\log n).$$
--
--   This is property (i) of Framework 1 for FPL$^*$. Through Lemma 3 it gives the high-probability switching bound of BFPL$^*_\delta$.
--
--   **Formalization Note** The paper's FPL$^*_\varepsilon$ has $P_1(i)=+R(i)/\varepsilon$. For that variant the bound fails numerically (with $n=1000$, $\varepsilon=0.01$, $\tau=200$ it averages about 25.8 switches against a bound of 16.0). The statement is made for the sign-corrected perturbation $-R(i)/\varepsilon$, the exponential analogue of Kalai–Vempala's algorithm. The hypothesis $\varepsilon<1$ makes $1/(1-\varepsilon)$ meaningful. The expectation is a lower Lebesgue integral of the natural-valued switch count.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 13, Lemma 7

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem lemma_7 {n : ℕ} [NeZero n] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (τ : ℕ)
    (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) :
    ∫⁻ R, (switches τ (play (fplStar ε) R ℓ) : ℝ≥0∞) ∂(expLaw n)
      ≤ ENNReal.ofReal ((ε * τ + 2 * Real.log n) / (1 - ε)) := by sorry

end LimitedSwitching.HighProb
