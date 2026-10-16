-- Prove2me | Theorems.Thm_InterdepSOS_KHL_lemma_6_2
-- name    : InterdepSOS.KHL.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:30.319032+00:00
-- url     : https://prove2.me/theorems/d3cff317-a253-4e31-8d3d-63eed65f7dad
-- title:
--   Lemma 6.2, p. 20 — Random Threshold gives a (k−1)-approximation to the SELF component
-- statement:
--   Let $v$ be SOS valuations satisfying the standing assumptions on the grid $\{0,\dots,k-1\}^n$, let the Random Threshold allocations $\bar T^{\ell}$ be produced by a maximizing selector as in the definition of the mechanism, let $\mathbf s$ be a grid profile and $T$ a feasible allocation. Write
--   $$\mathrm{RT}(\mathbf s)=\frac1{k-1}\sum_{\ell=1}^{k-1}\sum_i v_{i\bar T^{\ell}_i}(\mathbf s)$$
--   for the expected welfare of Random Threshold at the truthful profile, with $\ell$ uniform in $\{1,\dots,k-1\}$. Then
--   $$\mathsf{SELF}(T,\mathbf s)=\sum_{\ell=1}^{k-1}\sum_{i\,:\,s_i=\ell}v_{iT_i}(\mathbf 0_{-i},s_i)\;\le\;(k-1)\,\mathrm{RT}(\mathbf s).$$
--
--   This is the half of the welfare decomposition (7) that Random Threshold covers.
--
--   **Formalization Note** The paper states the lemma for the SELF component of a welfare-maximizing allocation; it is stated here for every feasible allocation $T$. For $k=1$ both sides are $0$ (the sum over $\ell$ is empty and Lean's $1/0=0$).
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 20, Lemma 6.2

import Mathlib
import Definitions.Def_InterdepSOS_KHL_Setting
import Definitions.Def_InterdepSOS_KHL_Mechanisms

namespace InterdepSOS.KHL
theorem lemma_6_2 {n m : ℕ} (k : ℕ) (v : Valuation n m)
    (hv : IsCombValuation k v) (hsos : ∀ i T, IsSOS k (v i T))
    (rtSel : ℕ → Signal n → Allocation n m) (hrt : IsRTSelector k v rtSel)
    (s : Signal n) (hs : InGrid k s) (T : Allocation n m) (hT : IsAllocOn Finset.univ T) :
    self k v T s ≤ ((k : ℝ) - 1) * rtAvg k v rtSel s := by sorry
end InterdepSOS.KHL
