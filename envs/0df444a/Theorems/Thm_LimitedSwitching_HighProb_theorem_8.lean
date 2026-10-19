-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_theorem_8
-- name    : LimitedSwitching.HighProb.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:07.397984+00:00
-- url     : https://prove2.me/theorems/147549d2-c632-4469-8c9c-17fa9e8ca5e0
-- title:
--   Theorem 8, p. 13 (FPL* sign corrected; N = ⌈log 2/δ⌉) — BFPL*_δ has Regret_T, Switches_T ≤ O(√(T log n log 1/δ)) w.p. ≥ 1 − δ
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $T\ge1$, $n\ge2$ and $\delta\in(0,\tfrac12)$. Let BFPL$^*_\delta$ be Framework 1 applied to the sign-corrected FPL$^*_\varepsilon$, with $N=\lceil\log(2/\delta)\rceil$, $\varepsilon=\tfrac12\sqrt{N\log n/T}$ and $S'=135\sqrt{T\log n/N}$, run with independent vectors of i.i.d. standard exponentials, one for each epoch. Then for every fixed loss sequence $(\ell_t)$ with values in $[0,1]$,
--
--   $$\mathbb P\Big(\mathrm{Regret}_T(\mathrm{BFPL}^*_\delta)\le C\sqrt{T\log n\log(1/\delta)}\ \text{ and }\ \mathrm{Switches}_T(\mathrm{BFPL}^*_\delta)\le C\sqrt{T\log n\log(1/\delta)}\Big)\ge1-\delta.$$
--
--   This is the paper's first explicit algorithm with simultaneous high-probability bounds on regret and switching. It establishes Theorem 1 for $n\ge2$.
--
--   **Formalization Note** The $O(\cdot)$ is an absolute constant $C$, chosen before $T$, $n$ and $\delta$. The statement bounds the outer measure of the failure event by $\delta$. Two corrections apply: the perturbation is $-R/\varepsilon$ (see Lemma 7), and $N=\lceil\log(2/\delta)\rceil$ replaces the real $\log(2/\delta)$ in $\varepsilon$ and $S'$. The hypothesis $n\ge2$ is the one of Lemma 9, which the proof uses. For $n=1$ the parameter $\varepsilon$ is $0$.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 13, Theorem 8 (BFPL*_δ defined p. 13); proof p. 14

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem theorem_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (T n : ℕ) [NeZero n], 1 ≤ T → 2 ≤ n →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ℓ : ℕ → Fin n → ℝ, IsLossSeq ℓ →
        bfplLaw n {ω | ¬ (regret T ℓ (play (bfplStar T n δ) ω ℓ)
              ≤ C * √(T * Real.log n * Real.log (1 / δ)) ∧
            (switches T (play (bfplStar T n δ) ω ℓ) : ℝ)
              ≤ C * √(T * Real.log n * Real.log (1 / δ)))}
          ≤ ENNReal.ofReal δ := by sorry

end LimitedSwitching.HighProb
