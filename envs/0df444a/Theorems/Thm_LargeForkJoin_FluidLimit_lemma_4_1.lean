-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_1
-- name    : LargeForkJoin.FluidLimit.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:08.54319+00:00
-- url     : https://prove2.me/theorems/1a3319ff-aeef-47f0-9448-7280d7429986
-- title:
--   Lemma 4.1, p. 17 — oscillation of the empty-start maximum queue bounded by increments of R̃_i
-- statement:
--   This is a deterministic, pathwise estimate on the maximum queue length of the fork-join system started empty.
--
--   Fix $N\ge1$, a sample point, $t>0$ and $\delta>0$. Write $Q(s)=Q^{(N)}_{(\alpha,\beta)}(sN^3\log N)$ for the maximum queue length (2.1) of the system with $Q^{(N)}_{(\alpha,\beta)}(0)=0$ and $\tilde R_i(s)=\tilde R_i^{(N)}(sN^3\log N)$ for the random walk of Definition 4.1. Then
--   $$
--   \sup_{t\le s\le t+\delta}\left|\frac{Q(s)}{N\log N}-\frac{Q(t)}{N\log N}\right|\le\sup_{t\le s\le t+\delta}\max_{i\le N}\big(\tilde R_i(s)-\tilde R_i(t)\big)+2\sup_{t\le s\le t+\delta}\max_{i\le N}\big(\tilde R_i(t)-\tilde R_i(s)\big).
--   $$
--
--   The estimate reduces the tightness of the empty-start part of the queue (Lemma 4.11) to the oscillations of $N$ random walks.
--
--   **Formalization Note** The suprema on the right are replaced by arbitrary upper bounds $a,b$: if $\tilde R_i(s)-\tilde R_i(t)\le a$ and $\tilde R_i(t)-\tilde R_i(s)\le b$ for all $s\in[t,t+\delta]$ and all servers $i$, then $|Q(s)-Q(t)|/(N\log N)\le a+2b$ for all $s\in[t,t+\delta]$. Since only finitely many values occur, this is equivalent to (4.7) and avoids real suprema. Times are evaluated at $\lfloor sN^3\log N\rfloor$; servers are indexed from $0$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 17, Lemma 4.1 (4.7)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_1 {Ω : Type*} (M : ForkJoin Ω) (α : ℝ) (N : ℕ) (ω : Ω) (t δ : ℝ)
    (hN : 0 < N) (ht : 0 < t) (hδ : 0 < δ) (a b : ℝ)
    (ha : ∀ s ∈ Set.Icc t (t + δ), ∀ i : Fin N,
      Rtil M α N i (tau N s) ω - Rtil M α N i (tau N t) ω ≤ a)
    (hb : ∀ s ∈ Set.Icc t (t + δ), ∀ i : Fin N,
      Rtil M α N i (tau N t) ω - Rtil M α N i (tau N s) ω ≤ b) :
    ∀ s ∈ Set.Icc t (t + δ),
      |maxQueueEmpty M N (tau N s) ω / scale N - maxQueueEmpty M N (tau N t) ω / scale N| ≤
        a + 2 * b := by sorry
end LargeForkJoin.FluidLimit
