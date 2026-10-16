-- Prove2me | Theorems.Thm_InterdepSOS_KHL_rt_ic_ir
-- name    : InterdepSOS.KHL.rt_ic_ir
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:27.436992+00:00
-- url     : https://prove2.me/theorems/2d4c0090-debd-48a5-bc43-d35ea681a67b
-- title:
--   §6.1, proof of ex-post IC-IR, p. 20 — every Random Threshold component is ex-post IC and IR
-- statement:
--   Let $v$ satisfy the standing assumptions on the grid $\{0,\dots,k-1\}^n$, and let the Random Threshold allocation be produced by a selector returning, at every grid profile and for every threshold $\ell\in\{1,\dots,k-1\}$, a feasible allocation to the high agents $N_{\ge\ell}$ that maximizes $\sum_{i\in N_{\ge\ell}}v_{iS_i}(\mathbf s_{N_{<\ell}},\ell_{N_{\ge\ell}})$, as a function of $\ell$ and of the proxy profile only. Let agent $i$ receiving the bundle $\bar T_i$ pay
--   $$v_{i\bar T_i}(\mathbf s_{-i},s_i=\ell-1).$$
--   Then for every $\ell\in\{1,\dots,k-1\}$ this deterministic mechanism is ex-post incentive compatible and ex-post individually rational on the grid.
--
--   Together with the corresponding statement for Random Sampling, this gives the incentive half of Theorem 6.1: k-HL is universally ex-post IC-IR.
--
--   **Formalization Note** The payment is evaluated at the reported profile with agent $i$'s own report replaced by $\ell-1$; it is $0$ for an agent receiving $\emptyset$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 20, §6.1, proof of ex-post IC-IR, second paragraph

import Mathlib
import Definitions.Def_InterdepSOS_KHL_Setting
import Definitions.Def_InterdepSOS_KHL_Mechanisms

namespace InterdepSOS.KHL
theorem rt_ic_ir {n m : ℕ} (k : ℕ) (v : Valuation n m) (hv : IsCombValuation k v)
    (rtSel : ℕ → Signal n → Allocation n m) (hrt : IsRTSelector k v rtSel) :
    ∀ ℓ ∈ Finset.Icc 1 (k - 1),
      IsExPostIC k v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ) ∧
        IsExPostIR k v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ) := by sorry
end InterdepSOS.KHL
