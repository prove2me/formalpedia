-- Prove2me | Theorems.Thm_InterdepSOS_KSS_theorem_6_5
-- name    : InterdepSOS.KSS.theorem_6_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:33.506432+00:00
-- url     : https://prove2.me/theorems/fe7dec4b-215f-415a-ab35-2e238e7ff95f
-- title:
--   Theorem 6.5, p. 23 — k-SS is universally ex-post IC-IR and a (2 log₂k + 4)-approximation to the optimal welfare for strong-SOS valuations
-- statement:
--   Consider a combinatorial auction with $n$ agents, $m$ items and single-dimensional signals in $\{0,1,\dots,k-1\}$, $k=2^q$, where every valuation $v_{iT}$ is strong-SOS. Fix any selectors implementing the argmax of Random Bucket and of Random Sampling. Then mechanism k-SS (Random Bucket with probability $p_{RB}=\frac{\log_2 k}{\log_2 k+2}$, Random Sampling otherwise) satisfies:
--
--   1. every Random Bucket component (each bucket index $\ell\in\{1,\dots,\log_2 k\}$, with its payments) is ex-post IC and ex-post IR;
--   2. every Random Sampling component (each partition $B$, no payments) is ex-post IC and ex-post IR;
--   3. for every grid profile $\mathbf s$ and every feasible allocation $T^*$ of the items,
--   $$\sum_i v_{iT^*_i}(\mathbf s)\;\le\;(2\log_2 k+4)\,\mathbb E[\text{welfare of k-SS at }\mathbf s].$$
--
--   Parts 1–2 say k-SS is universally ex-post IC-IR; part 3, applied to a welfare-maximizing $T^*$, is the $(2\log_2 k+4)$-approximation to the optimal social welfare. Compared with the $(k+3)$ ratio for SOS valuations, strong-SOS brings the dependence on the number of signal values down to logarithmic.
--
--   **Formalization Note** Signal space $\{0,\dots,k-1\}$ with $k=2^q$ and $\log_2 k=q$ (the buckets of Random Bucket cover the signals only when $k$ is a power of two). The approximation is stated in $\forall$-form over all feasible allocations, with true values at the truthful profile, avoiding a supremum. The only shape hypothesis is strong-SOS; SOS is a consequence. The mechanism's expected welfare is the k-SS mixture as defined in `kssWelfare`.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 23, Theorem 6.5

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting
import Definitions.Def_InterdepSOS_KSS_Mechanisms

namespace InterdepSOS.KSS
theorem theorem_6_5 {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (hv : InterdepSOS.KHL.IsCombValuation (2 ^ q) v) (hss : ∀ i T, IsStrongSOS (2 ^ q) (v i T))
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrb : IsRBSelector q v rbSel)
    (rsSel : Finset (Fin n) → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrs : InterdepSOS.KHL.IsRSSelector (2 ^ q) v rsSel) :
    (∀ ℓ ∈ Finset.Icc 1 q,
        InterdepSOS.KHL.IsExPostIC (2 ^ q) v (rbAlloc rbSel ℓ) (rbPay v rbSel ℓ) ∧
        InterdepSOS.KHL.IsExPostIR (2 ^ q) v (rbAlloc rbSel ℓ) (rbPay v rbSel ℓ)) ∧
    (∀ B : Finset (Fin n),
        InterdepSOS.KHL.IsExPostIC (2 ^ q) v (InterdepSOS.KHL.rsAlloc rsSel B) 0 ∧ InterdepSOS.KHL.IsExPostIR (2 ^ q) v (InterdepSOS.KHL.rsAlloc rsSel B) 0) ∧
    ∀ s : InterdepSOS.KHL.Signal n, InterdepSOS.KHL.InGrid (2 ^ q) s → ∀ Tstar : InterdepSOS.KHL.Allocation n m, InterdepSOS.KHL.IsAllocOn Finset.univ Tstar →
      InterdepSOS.KHL.welfare v Tstar s ≤ (2 * q + 4) * kssWelfare q v rbSel rsSel s := by sorry
end InterdepSOS.KSS
