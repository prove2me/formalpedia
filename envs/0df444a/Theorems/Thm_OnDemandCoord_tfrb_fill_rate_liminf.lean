-- Prove2me | Theorems.Thm_OnDemandCoord_tfrb_fill_rate_liminf
-- name    : OnDemandCoord.tfrb_fill_rate_liminf
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:26.738706+00:00
-- url     : https://prove2.me/theorems/ab051910-f736-4a1e-b8d7-7c7923988832
-- title:
--   Step 1 of Lemma 1: the TFRB policy delivers every feasible fill rate as $T\to\infty$
-- statement:
--   **Step 1 of the proof of Lemma 1** (§A.4.1, pp. A3–A5). Let $S\ge0$, any $Q$, and $\beta$ feasible for the linear program (8) at $(Q,S)$. For all run data and every firm $i$,
--   $$\liminf_{T\to\infty}\ \mathbb E\big[A_i(\hat X,S)\big]\ \ge\ \beta_i\,\mathbb E[\hat X_i],$$
--   where $A$ is drawn from the TFRB policy $\kappa_T$ with target fill rates $\beta$ and $\hat X=(X-Q)^+$. In the Lean statement the liminf is written with $\varepsilon$: for every $\varepsilon>0$, eventually in $T$, $\mathbb E[A_i]\ge\beta_i\mathbb E[\hat X_i]-\varepsilon$.
--
--   This is the approachability property of Algorithm 1 that the "moreover" part of Lemma 1 rests on.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - reading: E[A_i] ≥ β_i E[X̂_i] 'for large enough T' → liminf_{T→∞} E[A_i] ≥ β_i E[X̂_i]; reason: Algorithm 1 takes T 'a large number' and the proof is an approachability limit; at a finite T the bound can fail (paper.md item 3)
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), §A.4.1, Step 1 of the proof of Lemma 1, pp. A3–A5 (PDF 35–37)

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Step 1 of the proof of Lemma 1**, §A.4.1, pp. A3–A5 (PDF 35–37), Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13). For any
workforce `s ≥ 0`, any `Q`, any `β` feasible for (8) and all run data, the TFRB policy delivers at
least `β_i E[X̂_i]` to firm `i` in the limit:
`liminf_{T → ∞} E[A_i(X̂, s)] ≥ β_i E[X̂_i]`, written with `ε`.

**Formalization Note.** The `ε` form is the `liminf` inequality; it needs no boundedness side
condition. Allocations lie in `[0, s]`, so no moment of `X` beyond the first is used. -/
theorem tfrb_fill_rate_liminf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Q : Fin n → ℝ) (s : ℝ) (hs : 0 ≤ s) (β : Fin n → ℝ) (hβ : M.IsFeasibleLP Q s β)
    (run : RunData n s) (i : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      β i * M.mean Q i - ε ≤ M.expAlloc (M.tfrb Q s β run T) Q s i := by sorry

end OnDemandCoord
