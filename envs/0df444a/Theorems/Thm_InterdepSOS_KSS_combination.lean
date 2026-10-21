-- Prove2me | Theorems.Thm_InterdepSOS_KSS_combination
-- name    : InterdepSOS.KSS.combination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:28.593986+00:00
-- url     : https://prove2.me/theorems/43f6ecba-284b-4d08-b4d2-27ad271540ba
-- title:
--   §6.2, proof of Theorem 6.5, p. 23 — SELF + OTHER ≤ (2 log₂k + 4) times the expected welfare of k-SS
-- statement:
--   Let $k=2^q$, let $v$ be a combinatorial valuation on $\{0,\dots,k-1\}^n$ that is strong-SOS for every agent and bundle, and fix selectors implementing the argmax of Random Bucket and of Random Sampling. For every grid profile $\mathbf s$ and every feasible allocation $T$ of the items to all agents,
--   $$\mathsf{SELF}(T,\mathbf s)+\mathsf{OTHER}(T,\mathbf s)\;\le\;(2\log_2 k+4)\,\mathbb E[\text{welfare of k-SS at }\mathbf s],$$
--   where k-SS runs Random Bucket with probability $p_{RB}=\frac{\log_2 k}{\log_2 k+2}$ and Random Sampling with probability $1-p_{RB}$, and welfare is measured with true values under truthful reports.
--
--   This is the combination step of the proof of Theorem 6.5: Random Bucket covers SELF up to $2\log_2 k$ (Lemma 6.4), Random Sampling covers OTHER up to $4$ (Lemma 6.3), and the weights $p_{RB}$ and $1-p_{RB}$ balance the two.
--
--   **Formalization Note** $k=2^q$ and $\log_2 k=q$. The step contains the content of Lemma 6.3 (Random Sampling 4-approximates OTHER under SOS, which follows from strong-SOS); that lemma is posed in the companion mission on k-HL and not restated here. At $q=0$ the claim reduces to $\mathsf{OTHER}\le 4\,\mathbb E_B[\cdot]$, since $\mathsf{SELF}=0$ and $p_{RB}=0$. It is posed for every feasible $T$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 23, §6.2, proof of Theorem 6.5, display

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting
import Definitions.Def_InterdepSOS_KSS_Mechanisms

namespace InterdepSOS.KSS
theorem combination {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (hv : InterdepSOS.KHL.IsCombValuation (2 ^ q) v) (hss : ∀ i T, IsStrongSOS (2 ^ q) (v i T))
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrb : IsRBSelector q v rbSel)
    (rsSel : Finset (Fin n) → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrs : InterdepSOS.KHL.IsRSSelector (2 ^ q) v rsSel)
    (s : InterdepSOS.KHL.Signal n) (hs : InterdepSOS.KHL.InGrid (2 ^ q) s) (T : InterdepSOS.KHL.Allocation n m) (hT : InterdepSOS.KHL.IsAllocOn Finset.univ T) :
    InterdepSOS.KHL.self (2 ^ q) v T s + InterdepSOS.KHL.other v T s ≤ (2 * q + 4) * kssWelfare q v rbSel rsSel s := by sorry
end InterdepSOS.KSS
