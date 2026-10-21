-- Prove2me | Theorems.Thm_InterdepSOS_KSS_lemma_6_4
-- name    : InterdepSOS.KSS.lemma_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:34.465072+00:00
-- url     : https://prove2.me/theorems/59e0887d-9ce2-4f8d-8587-0388d85d5048
-- title:
--   Lemma 6.4, p. 22 — Random Bucket is ex-post IC-IR and a 2 log₂k approximation to SELF for strong-SOS valuations
-- statement:
--   Let $k=2^q$ and let $v$ be a combinatorial valuation on $\{0,\dots,k-1\}^n$ that is strong-SOS for every agent and bundle. Fix any selector that implements the argmax of Random Bucket. Then:
--
--   1. for every bucket index $\ell\in\{1,\dots,q\}$, the deterministic Random Bucket mechanism with index $\ell$ (allocation $\bar T^\ell$, payment $v_{i\bar T^\ell_i}(\mathbf s_{-i},2^{\ell-1}-1)$) is ex-post IC and ex-post IR;
--   2. for every grid profile $\mathbf s$ and every feasible allocation $T$ of the items to all agents,
--   $$\mathsf{SELF}(T,\mathbf s)\;\le\;2\sum_{\ell=1}^{q}\sum_i v_{i\bar T^{\ell}_i(\mathbf s)}(\mathbf s).$$
--
--   Since $\ell$ is uniform in $\{1,\dots,q\}$, the right-hand side is $2\log_2 k$ times the expected welfare of Random Bucket, so part 2 is the "$2\log_2 k$ approximation to the SELF component".
--
--   **Formalization Note** IC-IR is universal: it is stated for each deterministic component. The approximation is written multiplied out, $\mathsf{SELF}\le 2\sum_\ell W_\ell$, which equals $2q\cdot\frac1q\sum_\ell W_\ell$ for $q\ge1$ and avoids the division at $q=0$, where both sides are $0$. The paper takes $T=T^*$ welfare-maximizing; the statement is posed for every feasible $T$, which the proof's argument covers. The paper's proof writes $\ell\in\{1,\dots,k-1\}$ for $\ell\in\{1,\dots,\log_2 k\}$ and its last display writes $v(\mathbf 0_{-i},s_i)$ where the bound established is with $2^{\ell-1}_i$; the statement is unaffected. $k=2^q$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 22, Lemma 6.4

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting
import Definitions.Def_InterdepSOS_KSS_Mechanisms

namespace InterdepSOS.KSS
theorem lemma_6_4 {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (hv : InterdepSOS.KHL.IsCombValuation (2 ^ q) v) (hss : ∀ i T, IsStrongSOS (2 ^ q) (v i T))
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrb : IsRBSelector q v rbSel) :
    (∀ ℓ ∈ Finset.Icc 1 q,
        InterdepSOS.KHL.IsExPostIC (2 ^ q) v (rbAlloc rbSel ℓ) (rbPay v rbSel ℓ) ∧
        InterdepSOS.KHL.IsExPostIR (2 ^ q) v (rbAlloc rbSel ℓ) (rbPay v rbSel ℓ)) ∧
    ∀ s : InterdepSOS.KHL.Signal n, InterdepSOS.KHL.InGrid (2 ^ q) s → ∀ T : InterdepSOS.KHL.Allocation n m, InterdepSOS.KHL.IsAllocOn Finset.univ T →
      InterdepSOS.KHL.self (2 ^ q) v T s ≤ 2 * ∑ ℓ ∈ Finset.Icc 1 q, InterdepSOS.KHL.welfare v (rbAlloc rbSel ℓ s) s := by sorry
end InterdepSOS.KSS
