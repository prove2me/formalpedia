-- Prove2me | Theorems.Thm_OWMR_fifo_feasible
-- name    : OWMR.fifo_feasible
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:20.934256+00:00
-- url     : https://prove2.me/theorems/c62ddaa5-0ca3-4afc-b2a0-7d4b2aa670a1
-- title:
--   $\pi_{\rm FIFO}$ is nonanticipative and feasible for every choice with $s_i\le S_i$ and $s_0\le S_0$
-- statement:
--   Fix a network $N$ under the standing assumptions, a valid initial state $x$, and FIFO choices $c$ with $s_i\le S_i$ for every $i$ and $s_0\le S_0$. Then the deterministic FIFO policy $\pi_{\rm FIFO}$ of Definition 1, with the initialization of Appendix B, is
--
--   1. nonanticipative: its supplier order and dispatches in period $t$ depend on the demand sequence only through $D_0,\ldots,D_{t-1}$; and
--   2. feasible: for every demand sequence and period $t$, the supplier order and all dispatches are nonnegative, and the total dispatch $\sum_iq_{i,t}$ does not exceed the warehouse stock available in period $t$, the stock left from period $t-1$ plus the supplier arrival of period $t$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 3, Definition 1 (FIFO Policy) and the policy class of (2); Appendix B, Step 1 (initialization); Theorem D.1 (DFR Demand), p. E.24 ("is nonanticipative and feasible").

import Definitions.Def_owmr_fifo_policy

open scoped ENNReal NNReal

namespace OWMR
theorem fifo_feasible {n : ℕ} (N : Network n) (hN : N.Standing) (x : InitState n) (hx : x.Valid)
    (c : FIFOChoice n) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : c.s0 ≤ c.S0) :
    (fifoPolicy N x c).toPolicy.Nonanticipative ∧ (fifoPolicy N x c).toPolicy.Feasible N x := by sorry
end OWMR
