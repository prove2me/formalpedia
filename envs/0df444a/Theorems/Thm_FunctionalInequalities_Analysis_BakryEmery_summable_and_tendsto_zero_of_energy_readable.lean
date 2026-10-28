-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_summable_and_tendsto_zero_of_energy_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_energy_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:28.990936+00:00
-- url     : https://prove2.me/theorems/4b5372cd-579f-4bd0-914c-123a1ea1de17
-- title:
--   Summability and Vanishing of an Energy Sequence
-- statement:
--   This formalizes the summation conclusion of Corollary 3.5 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $L,\chi,v:\mathbb N\to\mathbb R$ and let $a\in\mathbb R$. Assume:
--
--   1. $a>0$.
--   2. $L_i\ge0$, $\chi_i\ge0$, and $v_i\ge0$ for every $i\in\mathbb N$.
--   3. For every $i$,
--      $$L_{i+1}+\chi_i+a v_i\le L_i.$$
--
--   Then both series $\sum_i v_i$ and $\sum_i\chi_i$ are summable, and
--
--   $$v_i\longrightarrow0\qquad(i\to\infty).$$
--
--   This is the abstract telescoping argument underlying the vanishing of the gradient-energy sequence in the tensor-energy iteration.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem summable_and_tendsto_zero_of_energy {L χ v : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
--       (hL : ∀ i, 0 ≤ L i) (hχ : ∀ i, 0 ≤ χ i) (hv : ∀ i, 0 ≤ v i)
--       (h45 : ∀ i, L (i + 1) + χ i + a * v i ≤ L i) :
--       Summable v ∧ Summable χ ∧ Tendsto v atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/TensorEnergy`](https://prove2.me/theorems/045db875-0e3b-41e8-bc31-c96740379ee1).
--
--   [Source excerpt, lines 352–355](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/TensorEnergy.lean#L352-L355) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Corollary 3.5, p. 13. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/TensorEnergy.lean#L350-L381 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.TensorEnergy`, declaration `FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_energy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_TensorEnergy

open MeasureTheory Filter Topology
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

theorem FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_energy_readable {L χ v : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hL : ∀ i, 0 ≤ L i) (hχ : ∀ i, 0 ≤ χ i) (hv : ∀ i, 0 ≤ v i)
    (h45 : ∀ i, L (i + 1) + χ i + a * v i ≤ L i) :
    Summable v ∧ Summable χ ∧ Tendsto v atTop (𝓝 0) := by sorry
