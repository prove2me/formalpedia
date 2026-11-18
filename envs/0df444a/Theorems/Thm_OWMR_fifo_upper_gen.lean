-- Prove2me | Theorems.Thm_OWMR_fifo_upper_gen
-- name    : OWMR.fifo_upper_gen
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:18.768505+00:00
-- url     : https://prove2.me/theorems/9d7a0c67-14da-4344-b242-80cdcfa50053
-- title:
--   Proposition 2 for arbitrary $(s,S)$ choices: $C(\pi_{\rm FIFO})\le c(f_{L_0};K_0+K_{\max},s_0,S_0)+\sum_i\bigl(c(F_i;K_i,s_i,S_i)+\mathrm{mirrorAvg}_i\bigr)$
-- statement:
--   Fix a network $N$ with $n\ge1$ retailers under the standing assumptions, a valid initial state $x$, and FIFO choices $c=(s_i,S_i,a_i,s_0,S_0)$ with $s_i\le S_i$ for every $i$ and $s_0\le S_0$; no optimality of the choices is assumed. Then the deterministic FIFO policy of Definition 1, with the initialization of Appendix B, satisfies
--   $$C(\pi_{\rm FIFO})\le c\bigl(f_{L_0};K_0+K_{\max},s_0,S_0\bigr)+\sum_i\Bigl(c\bigl(F_i;K_i,s_i,S_i\bigr)+\mathrm{mirrorAvg}_i(s_i,S_i,a_i)\Bigr),$$
--   where $c(f;K,s,S)$ (`ssAvgCost`) is the long-run average cost of the $(s,S)$ policy with setup cost $K$ per order and cost $f$ of the post-order position, $f_{L_0}(y)=\mathbb E\,\phi(y-D^{(L_0)})$ is the supplier's lead-time loss on aggregate demand, and $\mathrm{mirrorAvg}_i$ is retailer $i$'s long-run average mirror loss $\phi(a_i-\widehat P_{i,t})$.
--
--   This is Proposition 2 for general retailer and supplier $(s,S)$ choices, as used for $\pi_{\rm DFR}(\theta)$ in Step 4 of the proof of Theorem D.1.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 5, Proposition 2 (Physical Upper Bound), proved in Appendix B, as applied in Step 4 of the proof of Theorem D.1, p. E.27 ("the proof of Proposition 2 ... applies to these policies and centers").

import Definitions.Def_owmr_fifo_policy

open scoped ENNReal

namespace OWMR
theorem fifo_upper_gen {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (x : InitState n) (hx : x.Valid) (c : FIFOChoice n) (hsS : ∀ i, c.s i ≤ c.S i)
    (hs0 : c.s0 ≤ c.S0) :
    (fifoPolicy N x c).avgCost N x ≤ ssAvgCost N.aggregate N.fL0 (N.K0 + N.Kmax) c.s0 c.S0
      + ∑ i, (ssAvgCost (N.marginal i) (N.F i) (N.K i) (c.s i) (c.S i)
        + mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i)) := by sorry
end OWMR
