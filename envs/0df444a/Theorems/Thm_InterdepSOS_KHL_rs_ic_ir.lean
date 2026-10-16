-- Prove2me | Theorems.Thm_InterdepSOS_KHL_rs_ic_ir
-- name    : InterdepSOS.KHL.rs_ic_ir
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:45.298792+00:00
-- url     : https://prove2.me/theorems/b6c9dacc-2e47-4b16-a911-0cc55ba7b824
-- title:
--   §6.1, proof of ex-post IC-IR, p. 20 — every Random Sampling component is ex-post IC and IR
-- statement:
--   Let $v$ satisfy the standing assumptions on the grid $\{0,\dots,k-1\}^n$, and let the Random Sampling allocation be produced by a selector returning, at every grid profile and for every $B\subseteq[n]$, a feasible allocation to the agents of $B$ that maximizes $\sum_{i\in B}v_{iS_i}(\mathbf s_A,\mathbf 0_B)$, as a function of $B$ and of the proxy profile $(\mathbf s_A,\mathbf 0_B)$ only. Then for every $B\subseteq[n]$ the deterministic mechanism (Random Sampling with partition $(A,B)$, no payments) is
--
--   1. ex-post incentive compatible: no agent gains by misreporting her signal when the others report truthfully;
--   2. ex-post individually rational: truthful reporting gives every agent nonnegative utility.
--
--   Hence Random Sampling is universally ex-post IC-IR.
--
--   **Formalization Note** Utilities and reports range over the grid. The payment rule is identically $0$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 20, §6.1, proof of ex-post IC-IR, first paragraph

import Mathlib
import Definitions.Def_InterdepSOS_KHL_Setting
import Definitions.Def_InterdepSOS_KHL_Mechanisms

namespace InterdepSOS.KHL
theorem rs_ic_ir {n m : ℕ} (k : ℕ) (v : Valuation n m) (hv : IsCombValuation k v)
    (rsSel : Finset (Fin n) → Signal n → Allocation n m) (hrs : IsRSSelector k v rsSel) :
    ∀ B : Finset (Fin n),
      IsExPostIC k v (rsAlloc rsSel B) 0 ∧ IsExPostIR k v (rsAlloc rsSel B) 0 := by sorry
end InterdepSOS.KHL
