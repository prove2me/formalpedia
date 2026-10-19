-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_lemma_17
-- name    : LimitedSwitching.HighProb.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:05.020935+00:00
-- url     : https://prove2.me/theorems/a3f2e492-0125-40db-bbd8-e1577ac956a3
-- title:
--   Lemma 17, p. 27 (Be-The-Leader) — Σ_{t=0}^T ℓ_t(i_{t+1}) ≤ Σ_{t=0}^T ℓ_t(i) for every action i
-- statement:
--   Let $n\ge1$ and let $\ell_0,\ell_1,\dots$ be arbitrary real loss vectors on $[n]$. The Be-The-Leader rule plays at time $t$ the action
--   $$i_{t+1}=\operatorname*{arg\,min}_{j\in[n]}\sum_{s=0}^{t}\ell_s(j),$$
--   that is, the action Follow the Leader would play one round later. Ties go to the smallest index. Then for every $T\ge0$ and every action $i\in[n]$,
--
--   $$\sum_{t=0}^{T}\ell_t(i_{t+1})\le\sum_{t=0}^{T}\ell_t(i).$$
--
--   BTL is not an online algorithm, since it uses the current loss, but its negative regret is the key step in the proof of Lemma 5.
--
--   **Formalization Note** No sign or range condition is imposed on the losses: the lemma is applied to perturbed losses $\ell_t+P_{t+1}$. The paper's display writes $\ell_t$ inside the defining sum, a typo for $\ell_s$.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 27, Appendix C, Lemma 17

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem lemma_17 {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (T : ℕ) (i : Fin n) :
    ∑ t ∈ Finset.range (T + 1),
        ℓ t (argminFin (fun j => ∑ s ∈ Finset.range (t + 1), ℓ s j))
      ≤ ∑ t ∈ Finset.range (T + 1), ℓ t i := by sorry

end LimitedSwitching.HighProb
