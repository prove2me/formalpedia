-- Prove2me | Theorems.Thm_OWMR_fifo_engine_invariants
-- name    : OWMR.fifo_engine_invariants
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T06:36:42.744193+00:00
-- url     : https://prove2.me/theorems/4600105a-e768-4162-a17a-2288b06adf29
-- title:
--   Pathwise invariants of $\pi_{\rm FIFO}$: supplier rule on $Y_t$, $W_t\ge0$, $P_{i,t}\le\widehat P_{i,t}$, $W_t\Delta_t=0$, and the continuation charge (Lemma 7)
-- statement:
--   Fix a network $N$ satisfying the standing assumptions, a valid initial state $x$, FIFO choices $c$ with $s_i\le S_i$ and $s_0\le S_0$ (no optimality is assumed), and a deterministic demand path $d=(D_t)$. Write $B_i=I_i+\sum_{s<L_i}r_{i,s}$ for retailer $i$'s initial net inventory plus its prescribed pipeline, $w_s$ for the prescribed supplier pipeline, and $T_{\rm pipe}=\max(L_0,\max_iL_i)$. Let the activation flag be
--
--   $$\mathrm{act}_t\iff T_{\rm pipe}\le t+1\ \text{and}\ B_i-\sum_{s<t}D_{s,i}\le S_i\ \text{for all }i,$$
--
--   the start rule of Appendix B. Let the aggregate position be
--
--   $$Y_0=W+\sum_{s<L_0}w_s+\sum_i(B_i-a_i),\qquad Y_{t+1}=\bigl(S_0\ \text{if}\ \mathrm{act}_t\ \text{and}\ Y_t\le s_0,\ \text{else}\ Y_t\bigr)-\sum_iD_{t,i}.$$
--
--   Let the request positions be $\widehat P_{i,t}=B_i-\sum_{s<t}D_{s,i}$ before activation and $\widehat P_{i,t}=S_i$ in the first active period, and afterwards $\widehat P_{i,t+1}=\sigma_i(\widehat P_{i,t}-D_{t,i})$, where $\sigma_i(y)=S_i$ if $y\le s_i$ and $\sigma_i(y)=y$ otherwise. (The statement quantifies over any functions satisfying these recursions; they are unique.) Then, for the supplier orders $q_{0,t}$ and dispatches $q_{i,t}$ of $\pi_{\rm FIFO}$ along $d$, for all $t$, $i$ and $T$:
--
--   1. $q_{0,t}=(S_0-Y_t)\,\mathbf 1_{\{\mathrm{act}_t,\ Y_t\le s_0\}}$;
--   2. warehouse stock is nonnegative, $W_t\ge0$;
--   3. retailer $i$'s position after dispatches, $P_{i,t}=B_i+\sum_{r\le t}q_{i,r}-\sum_{r<t}D_{r,i}$, satisfies $P_{i,t}\le\widehat P_{i,t}$;
--   4. $W_t\sum_i(\widehat P_{i,t}-P_{i,t})=0$;
--   5. (Lemma 7) with $y_{i,t}=\widehat P_{i,t-1}-D_{t-1,i}$ the pre-request position,
--
--   $$\sum_{t<T}\sum_iK_i\mathbf 1_{\{q_{i,t}>0\}}\le\sum_{0<t<T}\mathbf 1_{\mathrm{act}_{t-1}}\sum_iK_i\mathbf 1_{\{y_{i,t}\le s_i,\ y_{i,t}<S_i\}}+K_{\max}\Bigl(n+L_0+\sum_{t<T}\mathbf 1_{\{q_{0,t}>0\}}\Bigr).$$
--
--   Items 3 and 4 are the queue invariants (23), $P_i=\widehat P_i-\Delta_i$ with $\Delta_i\ge0$ and $W\Delta=0$; item 5 is the continuation charge (26), with $N_{\rm init}\le L_0$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 5.1, queue invariants (23) and aggregate position (24), pp. 21-22; Lemma 7 (Continuation Charge), eq. (26), p. 22; start of the policy in Appendix B, Step 1, p. E.4.

import Definitions.Def_owmr_fifo_policy

open scoped ENNReal NNReal

namespace OWMR
theorem fifo_engine_invariants {n : ℕ} (N : Network n) (hN : N.Standing) (x : InitState n)
    (hx : x.Valid) (c : FIFOChoice n) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : c.s0 ≤ c.S0)
    (d : ℕ → DemandVec n) (act : ℕ → Prop) [DecidablePred act]
    (hact : ∀ t, act t ↔ (N.Tpipe ≤ t + 1 ∧ ∀ i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
    (Yp : ℕ → ℝ)
    (hY0 : Yp 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i))
    (hY : ∀ t, Yp (t + 1) = (if act t ∧ Yp t ≤ c.s0 then c.S0 else Yp t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
    (Ph : ℕ → Fin n → ℝ)
    (hPh0 : ∀ i, Ph 0 i = if act 0 then c.S i else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s)
    (hPh : ∀ t i, Ph (t + 1) i = if act (t + 1) then
        (if act t then (if Ph t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i
          else Ph t i - ((d t i : ℝ≥0) : ℝ)) else c.S i)
      else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        - ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ)) :
    (∀ t, (fifoPolicy N x c).toPolicy.order t () d
        = if act t ∧ Yp t ≤ c.s0 then c.S0 - Yp t else 0) ∧
    (∀ t, 0 ≤ Policy.whStock N x (fifoPolicy N x c).toPolicy () d t) ∧
    (∀ t i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + ∑ r ∈ Finset.range (t + 1), (fifoPolicy N x c).toPolicy.dispatch r () d i
        - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) ≤ Ph t i) ∧
    (∀ t, Policy.whStock N x (fifoPolicy N x c).toPolicy () d t
        * ∑ i, (Ph t i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + ∑ r ∈ Finset.range (t + 1), (fifoPolicy N x c).toPolicy.dispatch r () d i
          - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ))) = 0) ∧
    (∀ T, ∑ t ∈ Finset.range T, ∑ i, N.K i
          * (if 0 < (fifoPolicy N x c).toPolicy.dispatch t () d i then 1 else 0)
        ≤ ∑ t ∈ Finset.range T, (if 0 < t ∧ act (t - 1) then ∑ i, N.K i
            * (if Ph (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i
                ∧ Ph (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) < c.S i then 1 else 0) else 0)
          + N.Kmax * (n + N.L0 + ∑ t ∈ Finset.range T,
              (if 0 < (fifoPolicy N x c).toPolicy.order t () d then 1 else 0))) := by sorry
end OWMR
