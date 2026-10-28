-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_corollary_6
-- name    : LimitedSwitching.HighProb.corollary_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:01.158981+00:00
-- url     : https://prove2.me/theorems/1e1df39d-df43-40e6-9bab-c973ceff21fd
-- title:
--   Corollary 6, p. 13, for BFPL* as on p. 14 (corrected: + E) — Regret_T ≤ Switches_T + E + Σ_e max_i R_e(i)/ε pointwise
-- statement:
--   Let $n\ge1$, $\varepsilon>0$, any budget $S'$ and $T\ge1$, and let $(\ell_t)$ be a loss sequence with values in $[0,1]$. Let $\mathcal B$ be Framework 1 applied to FPL$^*_\varepsilon$ (perturbation $-R_e(i)/\varepsilon$ in epoch $e$), run with nonnegative perturbation vectors $R_0,R_1,\dots\in[0,\infty)^n$, one for each epoch. Let $E$ be the number of epochs used in rounds $1,\dots,T$. Then, pointwise,
--
--   $$\mathrm{Regret}_T(\mathcal B)\le\mathrm{Switches}_T(\mathcal B)+E+\sum_{e<E}\max_{i\in[n]}\frac{R_e(i)}{\varepsilon}.$$
--
--   This is the specialisation of Corollary 6 used in the proof of Theorem 8 (p. 14). Combined with Lemma 3, which bounds $E$, and Lemma 9, which bounds the sum of maxima, it gives the high-probability regret bound.
--
--   **Formalization Note** The term $+E$ is a correction: Corollary 6 sums Lemma 5 over the epochs, and Lemma 5 needs $M(\mathrm{Switches}+1)$ (see its note), with $M=1$ for losses in $[0,1]$. The general-perturbation form of Corollary 6 is not stated. Epochs are 0-based, so the sum runs over $e=0,\dots,E-1$.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 13, Corollary 6, as specialised in the proof of Theorem 8, p. 14, display

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem corollary_6 {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (hω : ∀ e i, 0 ≤ ω e i)
    (ε : ℝ) (hε : 0 < ε) (S' : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) :
    regret T ℓ (play (batch (fplStar ε) S') ω ℓ)
      ≤ (switches T (play (batch (fplStar ε) S') ω ℓ) : ℝ)
        + (numEpochs (fplStar ε) S' ω ℓ T : ℝ)
        + ∑ e ∈ Finset.range (numEpochs (fplStar ε) S' ω ℓ T),
            Finset.univ.sup' Finset.univ_nonempty (ω e) / ε := by sorry

end LimitedSwitching.HighProb
