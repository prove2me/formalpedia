-- Prove2me | Theorems.Thm_OWMR_selected_policy
-- name    : OWMR.selected_policy
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T20:47:31.655866+00:00
-- url     : https://prove2.me/theorems/0381b89b-185e-4336-beb4-b161f70a5c43
-- title:
--   Corollary 1 (selected policy): FIFO or consolidation, whichever applies, costs at most min{13/3+32/(57m), max{9/4+1/(4m), 1+K_max/K_0}} times OPT
-- statement:
--   Let $N$ be a one-warehouse multi-retailer network with $n\ge1$ retailers under the standing assumptions of Section 3, with associated retailer demands in each period, $H_i\ge h$ for every retailer and $p\ge h$. Set $m=\min_iH_i/h$, $\gamma_m=9/4+1/(4m)$ and $\bar\gamma_m=13/3+32/(57m)$. Fix a valid initial state, choices for $\pi_{\rm FIFO}$ satisfying Definition 1 (`IsFIFOChoice`) and choices for $\pi^{(m)}_{\rm con}$ satisfying Definition 2 with parameter $m$ (`IsConChoice N m`).
--
--   1. **Corollary 1.** If $K_0>0$, the policy $\pi_{\rm select}$ that uses $\pi_{\rm FIFO}$ if $1+K_{\max}/K_0\le\bar\gamma_m$ and $\pi^{(m)}_{\rm con}$ otherwise satisfies $C(\pi_{\rm select})\le\min\{\bar\gamma_m,\max\{\gamma_m,1+K_{\max}/K_0\}\}\,\mathrm{OPT}$.
--   2. **The remark after Corollary 1.** If $K_0=0$, using $\pi_{\rm FIFO}$ when $K_{\max}=0$ and $\pi^{(m)}_{\rm con}$ otherwise gives the factors $\gamma_m$ and $\bar\gamma_m$, respectively.
--
--   Costs are long-run expected average costs from the given initial state, and OPT is the optimal such cost over all feasible nonanticipative policies, as in Theorems 1 and 2.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 6, Corollary 1 (Selected Policy) and the remark after it on K_0 = 0, p. 30; it combines Theorem 1 (p. 10) and Theorem 2 (p. 29).

import Definitions.Def_owmr_fifo_policy
import Definitions.Def_owmr_consolidation_policy

open scoped ENNReal

namespace OWMR
theorem selected_policy {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (hA : N.Associated) (hH : ∀ i, N.h ≤ N.H i) (hp : N.h ≤ N.p)
    (m : ℝ) (hm : m = ⨅ i, N.H i / N.h)
    (x : InitState n) (hx : x.Valid) (cF : FIFOChoice n) (hcF : IsFIFOChoice N cF)
    (cC : ConChoice n) (hcC : IsConChoice N m cC) :
    (0 < N.K0 →
      (if 1 + N.Kmax / N.K0 ≤ 13 / 3 + 32 / (57 * m) then fifoPolicy N x cF
        else conPolicy N x cC).avgCost N x
      ≤ ENNReal.ofReal (min (13 / 3 + 32 / (57 * m))
          (max (9 / 4 + 1 / (4 * m)) (1 + N.Kmax / N.K0))) * OPT N x) ∧
    (N.K0 = 0 →
      (if N.Kmax = 0 then fifoPolicy N x cF else conPolicy N x cC).avgCost N x
      ≤ ENNReal.ofReal (if N.Kmax = 0 then 9 / 4 + 1 / (4 * m) else 13 / 3 + 32 / (57 * m))
        * OPT N x) := by sorry
end OWMR
