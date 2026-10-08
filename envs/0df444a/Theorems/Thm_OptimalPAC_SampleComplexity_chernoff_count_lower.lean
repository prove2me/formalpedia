-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_chernoff_count_lower
-- name    : OptimalPAC.SampleComplexity.chernoff_count_lower
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:28:18.05207+00:00
-- url     : https://prove2.me/theorems/5ec3b2ae-4d78-4788-adbf-08c7dcbfe53e
-- title:
--   Chernoff lower bound on the number of sample points in a set, event $E_i''$ (constants $23$, $7/10$, $\delta/9$)
-- statement:
--   Let $Q$ be a probability measure on $\mathcal X$, $E\subseteq\mathcal X$ a measurable set, $n\ge1$ and $\delta\in(0,1)$, and suppose
--   $$Q(E)\ge\frac{23}{n}\ln\left(\frac9\delta\right).$$
--   If $Z_1,\ldots,Z_n$ are independent with law $Q$ and $N=|\{t\le n: Z_t\in E\}|$, then with probability at least $1-\delta/9$,
--   $$N\ge\frac7{10}\,Q(E)\,n.$$
--
--   The proof of Theorem 2 applies this with $E=\mathrm{ER}(h_i)$ and $n=|S_i|=\lfloor m/4\rfloor$, under the conditional distribution given $h_i$ (which is independent of $S_i$); the resulting event is $E_i''$.
--
--   **Formalization Note** The paper's step is stated for the random set $\mathrm{ER}(h_i)$; this item is the fixed-set bound that the proof applies conditionally. The failure event $N<\frac7{10}Q(E)n$ is bounded in outer measure by $\delta/9$.
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, proof of Theorem 2, p. 9 (the event E_i'')

import Mathlib

open MeasureTheory

namespace OptimalPAC.SampleComplexity

/-- The Chernoff step of the proof of Theorem 2 (Hanneke 2016, p. 9, the event `E_i''`), for a
fixed set: if `Z₁, …, Z_n` are i.i.d. `Q`, `E` is measurable and
`Q(E) ≥ (23/n) ln(9/δ)`, then with probability at least `1 − δ/9` the number `N` of
indices `t` with `Z_t ∈ E` satisfies `N ≥ (7/10) Q(E) n`. -/
theorem chernoff_count_lower {X : Type*} [MeasurableSpace X] (Q : Measure X)
    [IsProbabilityMeasure Q] (E : Set X) (hE : MeasurableSet E) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hQE : 23 / (n : ℝ) * Real.log (9 / δ) ≤ (Q E).toReal) :
    Measure.pi (fun _ : Fin n => Q)
      {z | (({t : Fin n | z t ∈ E}.ncard : ℕ) : ℝ) < 7 / 10 * (Q E).toReal * n}
      ≤ ENNReal.ofReal (δ / 9) := by sorry

end OptimalPAC.SampleComplexity
