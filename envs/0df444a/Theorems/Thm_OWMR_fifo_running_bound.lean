-- Prove2me | Theorems.Thm_OWMR_fifo_running_bound
-- name    : OWMR.fifo_running_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T20:47:32.950267+00:00
-- url     : https://prove2.me/theorems/350a4afd-417e-4264-8da7-f3196f92f889
-- title:
--   Lemma 8 (FIFO holding and backlog bound): after initialization, every period satisfies hW_t+Σ_i F_i(P_it) ≤ φ(E_t)+Σ_i[F_i(P̂_it)+φ(a_i-P̂_it)]
-- statement:
--   Consider $\pi_{\rm FIFO}$ of Definition 1 (`fifoPolicy`) with choices satisfying Definition 1 (`IsFIFOChoice`), on a network under the standing assumptions, from a valid initial state, along any demand sequence. The predicate `act t` characterizes the periods after the initialization of Appendix B: all prescribed pipelines have arrived ($T_{\rm pipe}\le t+1$) and every retailer's position, after receipts, is at most its target $S_i$. The positions including outstanding requests $\widehat P_{i,t}$ (`Ph`) are pinned down by the retailers' rule: $\widehat P_{i,t}=S_i$ in the first such period, and thereafter $\widehat P_{i,t+1}$ is the post-request position of the $(s_i,S_i)$ rule applied to $\widehat P_{i,t}-D_{i,t}$ (before the initialization `Ph` is the natural position, which plays no role). Let $W_t$ be the warehouse stock after the dispatches of period $t$, $P_{i,t}$ retailer $i$'s net inventory plus stock in transit after those dispatches, $a_i$ the mirror centers, $E_t=W_t+\sum_i(P_{i,t}-a_i)$ as in (24), and $\phi(y)=hy^++py^-$. Then every period $t$ after the initialization satisfies
--   $$hW_t+\sum_iF_i(P_{i,t})\le\phi(E_t)+\sum_i\bigl[F_i(\widehat P_{i,t})+\phi(a_i-\widehat P_{i,t})\bigr].$$
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 5.2, Lemma 8 (FIFO Holding and Backlog Cost Bound), p. 23, with the queue invariants (23) and the aggregate position (24) of Section 5.1, p. 22, Definition 1 (p. 9) and the initialization of Appendix B (p. E.4).

import Definitions.Def_owmr_fifo_policy

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem fifo_running_bound {n : ℕ} (N : Network n) (hN : N.Standing) (x : InitState n)
    (hx : x.Valid) (c : FIFOChoice n) (hc : IsFIFOChoice N c)
    (d : ℕ → DemandVec n) (act : ℕ → Prop) [DecidablePred act]
    (hact : ∀ t, act t ↔ (N.Tpipe ≤ t + 1 ∧ ∀ i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
    (Ph : ℕ → Fin n → ℝ)
    (hPh0 : ∀ i, Ph 0 i = if act 0 then c.S i else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s)
    (hPh : ∀ t i, Ph (t + 1) i = if act (t + 1) then
        (if act t then (if Ph t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i
          else Ph t i - ((d t i : ℝ≥0) : ℝ)) else c.S i)
      else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        - ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ))
    (t : ℕ) (ht : act t) :
    let W := Policy.whStock N x (fifoPolicy N x c).toPolicy () d t
    let P : Fin n → ℝ := fun i => x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      + ∑ r ∈ Finset.range (t + 1), (fifoPolicy N x c).toPolicy.dispatch r () d i
      - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)
    let E := W + ∑ i, (P i - c.a i)
    N.h * W + ∑ i, N.F i (P i)
      ≤ whLoss N.h N.p E + ∑ i, (N.F i (Ph t i) + whLoss N.h N.p (c.a i - Ph t i)) := by sorry
end OWMR
