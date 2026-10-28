-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_lemma_5
-- name    : LimitedSwitching.HighProb.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:58.414318+00:00
-- url     : https://prove2.me/theorems/b4094132-b5a9-4579-858b-8bda03664b6e
-- title:
--   Lemma 5, p. 13 (corrected: M·(Switches_T + 1)) — pointwise regret bound for FPL with perturbations P_t
-- statement:
--   Let $n\ge1$ and $T\ge0$, and let $P_t(i)$ be arbitrary real perturbations and $\ell_t(i)$ arbitrary real losses. Let FPL play at round $t$ the (lowest-index) minimiser $i_t$ of $\sum_{s=0}^{t-1}(\ell_s(i)+P_{s+1}(i))$, with $\ell_0:=0$, for every $t\ge1$. In particular $i_{T+1}$ is the perturbed leader after round $T$. Let $M\ge0$ bound the loss differences: $|\ell_t(i)-\ell_t(j)|\le M$ for all $t\in\{1,\dots,T\}$ and all $i,j$. Then, pointwise,
--
--   $$\mathrm{Regret}_T(\mathrm{FPL})\le M\big(\mathrm{Switches}_T(\mathrm{FPL})+1\big)+\Big[\max_{i\in[n]}\sum_{t=1}^{T+1}P_t(i)\Big]-\sum_{t=1}^{T+1}P_t(i_t).$$
--
--   This is property (ii) of Framework 1 for FPL-type algorithms: regret is controlled by switching plus a perturbation term that does not depend on the adversary.
--
--   **Formalization Note** As printed, with $M\cdot\mathrm{Switches}_T$, the lemma is false. Take $T=1$, $n=2$, $P_1=(0,0.1)$, $P_t=0$ otherwise, and $\ell_1=(1,0)$: then the regret is $1$ while the printed right side is $0.1$. The printed proof (p. 27) bounds $\sum_{t=1}^T\mathbf 1(i_t\ne i_{t+1})$, which also counts a move to the never-played leader $i_{T+1}$. Hence $+1$. The paper's $M$ is the supremum of $|\ell(i)-\ell(i')|$ over losses; here $M$ is any bound for the given losses, which is at least as strong.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 13, Lemma 5 (M defined p. 12); proof p. 27, Appendix C

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem lemma_5 {n : ℕ} [NeZero n] (P : ℕ → Fin n → ℝ) (ℓ : ℕ → Fin n → ℝ) (T : ℕ) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |ℓ t i - ℓ t j| ≤ M) :
    regret T ℓ (fplPlay P ℓ)
      ≤ M * ((switches T (fplPlay P ℓ) : ℝ) + 1)
        + (⨆ i, ∑ t ∈ Finset.Icc 1 (T + 1), P t i)
        - ∑ t ∈ Finset.Icc 1 (T + 1), P t (fplPlay P ℓ t) := by sorry

end LimitedSwitching.HighProb
