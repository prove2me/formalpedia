-- Prove2me | Theorems.Thm_InterdepSOS_RSVCG_theorem_5_1
-- name    : InterdepSOS.RSVCG.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:27.771747+00:00
-- url     : https://prove2.me/theorems/8f179b91-9c57-4f7e-8d53-ca45d771660c
-- title:
--   Theorem 5.1, p. 17 — Random-Sampling VCG is universally ex-post IC-IR and a 4-approximation to the optimal welfare for separable SOS valuations
-- statement:
--   Consider a combinatorial auction with $n$ agents and $m$ items, multidimensional signals $s_{iT} \in \mathbb{R}_+$ and interdependent bundle valuations $v_{iT}(s_T)$ (Definition 2.10) that are separable SOS:
--   $$v_{iT}(s_T) = g_{-iT}(s_{-iT}) + h_{iT}(s_{iT})$$
--   with $g_{-iT}, h_{iT}$ weakly increasing and $g_{-iT}$ SOS (Definition 2.16). Run Random-Sampling VCG: split the agents uniformly at random into $A$ and $B$, allocate to $B$ an allocation maximising the proxy welfare $\sum_{i \in B} w_{iT_i}$ with $w_{iT} = v_{iT}(\tilde s_{iT}, \tilde s_{AT}, 0_{B-iT})$, and charge the VCG-style payments of §5. Then:
--
--   1. **Universal ex-post IC-IR.** For every partition $(A, B)$ the resulting deterministic mechanism is ex-post incentive compatible and ex-post individually rational.
--   2. **4-approximation.** For every true signal profile $s$, reported truthfully, and every feasible allocation $(S^*_1, \dots, S^*_n)$ of the items to all agents,
--   $$\sum_{i} v_{iS^*_i}(s_{S^*_i}) \le 4\, \mathbb{E}_B\Bigl[\sum_i v_{iT_i(B)}(s_{T_i(B)})\Bigr],$$
--   where $T_i(B)$ is the bundle RS-VCG gives agent $i$ under partition $B$ and $\mathbb{E}_B$ is the uniform average over the $2^n$ subsets $B$.
--
--   This is the main result of §5: the random-sampling idea of the single-parameter mechanism RS-V extends to combinatorial auctions with multidimensional signals once valuations are separable, with explicit payments analogous to VCG.
--
--   **Formalization Note** Both conclusions are claimed for every allocation selector returning a feasible maximiser of the proxy welfare. The approximation is stated for every feasible comparator allocation, with welfare measured at true values. Agents of $A$, and agents of $B$ allocated the empty bundle, pay $0$ (the paper defines payments only for winners); the empty bundle is worth $0$ and the monotonicity hypotheses are required for nonempty bundles.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 17, Theorem 5.1

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting
import Definitions.Def_InterdepSOS_RSVCG_Mechanism

namespace InterdepSOS.RSVCG

theorem theorem_5_1 {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc) :
    (∀ B : Finset (Fin n),
      IsExPostIC v (alloc B) (vcgPay v g alloc B) ∧
        IsExPostIR v (alloc B) (vcgPay v g alloc B)) ∧
    ∀ (s : Profile n m) (Tstar : Alloc n m), IsAllocOn Finset.univ Tstar →
      welfare v s Tstar ≤ 4 * avgB (fun B => welfare v s (alloc B s)) := by sorry

end InterdepSOS.RSVCG
