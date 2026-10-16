-- Prove2me | Theorems.Thm_InterdepSOS_KHL_theorem_6_1
-- name    : InterdepSOS.KHL.theorem_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:26.332984+00:00
-- url     : https://prove2.me/theorems/189dc620-0aea-4397-b061-414624850557
-- title:
--   Theorem 6.1, p. 20 — k-HL is universally ex-post IC-IR and a (k+3)-approximation to the optimal welfare for SOS valuations with k signal values
-- statement:
--   Consider a combinatorial auction with $n$ agents, $m$ items and a positive number $k$ of signal values, with single-dimensional signals $s_i\in\{0,1,\dots,k-1\}$, where the valuations $v_{iT}$ satisfy the standing assumptions (nonnegative, $v_{i\emptyset}\equiv0$, weakly increasing in every signal and strictly increasing in the own signal on nonempty bundles) and are SOS. Run the mechanism k-HL: with probability $p_{RT}=\frac{k-1}{k+3}$ run Random Threshold with $\ell$ uniform in $\{1,\dots,k-1\}$, otherwise Random Sampling with a uniformly random partition $(A,B)$; the allocations are produced by arbitrary maximizing selectors that depend on the reports only through the proxy data. Then:
--
--   1. for every threshold $\ell\in\{1,\dots,k-1\}$, Random Threshold with its payments $v_{i\bar T_i}(\mathbf s_{-i},s_i=\ell-1)$ is ex-post IC and ex-post IR;
--   2. for every $B\subseteq[n]$, Random Sampling without payments is ex-post IC and ex-post IR;
--   3. for every grid profile $\mathbf s$ and every feasible allocation $T^*$,
--   $$\sum_i v_{iT^*_i}(\mathbf s)\;\le\;(k+3)\Bigl(p_{RT}\cdot\frac1{k-1}\sum_{\ell=1}^{k-1}\sum_i v_{i\bar T^{\ell}_i}(\mathbf s)+(1-p_{RT})\cdot\frac1{2^n}\sum_{B\subseteq[n]}\sum_i v_{i\tilde T^{B}_i}(\mathbf s)\Bigr).$$
--
--   Items 1–2 say that k-HL is universally ex-post IC-IR; item 3 says that its expected welfare at the truthful profile, measured with true values, is at least a $1/(k+3)$ fraction of the optimal welfare.
--
--   **Formalization Note** The approximation is stated against every feasible allocation instead of an optimum, which is equivalent and avoids a supremum. The paper's "signal space of size $k$" is made explicit as $1\le k$; at $k=0$ the displayed mixing weight would be negative. For $k=1$, $p_{RT}=0$ and k-HL is Random Sampling.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 20, Theorem 6.1

import Mathlib
import Definitions.Def_InterdepSOS_KHL_Setting
import Definitions.Def_InterdepSOS_KHL_Mechanisms

namespace InterdepSOS.KHL
theorem theorem_6_1 {n m : ℕ} (k : ℕ) (hk : 1 ≤ k) (v : Valuation n m)
    (hv : IsCombValuation k v) (hsos : ∀ i T, IsSOS k (v i T))
    (rtSel : ℕ → Signal n → Allocation n m) (hrt : IsRTSelector k v rtSel)
    (rsSel : Finset (Fin n) → Signal n → Allocation n m) (hrs : IsRSSelector k v rsSel) :
    (∀ ℓ ∈ Finset.Icc 1 (k - 1),
        IsExPostIC k v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ) ∧
        IsExPostIR k v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ)) ∧
    (∀ B : Finset (Fin n),
        IsExPostIC k v (rsAlloc rsSel B) 0 ∧ IsExPostIR k v (rsAlloc rsSel B) 0) ∧
    ∀ s : Signal n, InGrid k s → ∀ Tstar : Allocation n m, IsAllocOn Finset.univ Tstar →
      welfare v Tstar s ≤ ((k : ℝ) + 3) * khlWelfare k v rtSel rsSel s := by sorry
end InterdepSOS.KHL
