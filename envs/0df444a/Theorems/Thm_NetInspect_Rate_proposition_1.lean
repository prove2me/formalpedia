-- Prove2me | Theorems.Thm_NetInspect_Rate_proposition_1
-- name    : NetInspect.Rate.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:09.408209+00:00
-- url     : https://prove2.me/theorems/7abbf57f-b1c7-48d8-9734-29026818b33d
-- title:
--   Proposition 1, p. 13 — max{0, b2(1 − b1/|T′|)} ≤ U*(b1,b2) ≤ b2(1 − b1/|S′|), attained by σ2(T′,b2) and σ1(S′,b1)
-- statement:
--   Let $\mathcal G$ be a detection model and let $b_1<n^*$ and $1\le b_2<m^*$. Then:
--
--   1. for every minimal set cover $S'$, enumerated without repetition as $x_0,\dots,x_{n-1}$,
--   $$
--   U^*(b_1,b_2)\le\max_{T\in\mathcal A_2}U(\sigma^1(S',b_1),T)=b_2\Bigl(1-\frac{b_1}{|S'|}\Bigr);
--   $$
--   2. for every set packing $T'$ of size $m\ge b_2$, enumerated without repetition as $y_0,\dots,y_{m-1}$,
--   $$
--   \max\Bigl\{0,\ b_2\Bigl(1-\frac{b_1}{|T'|}\Bigr)\Bigr\}=\min_{S\in\mathcal A_1}U(S,\sigma^2(T',b_2))\le U^*(b_1,b_2).
--   $$
--
--   Here $\sigma^1(S',b_1)$ and $\sigma^2(T',b_2)$ are the cyclic strategies of Lemma EC.3 and $U^*(b_1,b_2)$ is the value of $\Gamma(b_1,b_2)$. The proposition gives MSC/MSP-based bounds on the value and strategies attaining them; it is the main quantitative input of Theorem 1 and of the proof of Theorem 2.
--
--   **Formalization Note** $b_1<n^*$ and $b_2<m^*$ are the standing assumptions of §3.3 (p. 12). The hypothesis $b_2\ge 1$ is added: with $b_2=0$ the empty set would be a packing of size $\ge b_2$ and $\sigma^2(\emptyset,0)$ would not be a probability vector; the paper's base case is $b_2=1$.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, p. 13, Proposition 1; standing assumptions p. 12

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- Proposition 1 (p. 13), under the standing assumptions `b1 < n*`, `b2 < m*` of §3.3 and
`1 ≤ b2`: for every minimal set cover `S' = {x 0, …, x (n-1)}`,
`U*(b1, b2) ≤ max_{T∈A2} U(σ1(S', b1), T) = b2 (1 − b1/|S'|)`, and for every set packing
`T' = {y 0, …, y (m-1)}` with `m ≥ b2`,
`max{0, b2 (1 − b1/|T'|)} = min_{S∈A1} U(S, σ2(T', b2)) ≤ U*(b1, b2)`. -/
theorem proposition_1 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    (∀ (n : ℕ) (x : Fin n → V), Function.Injective x → G.IsMinimalSetCover (univ.image x) →
      G.worst1 b2 (cycStrat x b1) = (b2 : ℝ) * (1 - (b1 : ℝ) / (n : ℝ)) ∧
      G.gameValue b1 b2 ≤ (b2 : ℝ) * (1 - (b1 : ℝ) / (n : ℝ))) ∧
    (∀ (m : ℕ) (y : Fin m → E), Function.Injective y → G.IsSetPacking (univ.image y) → b2 ≤ m →
      G.best2 b1 (cycStrat y b2) = max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / (m : ℝ))) ∧
      max 0 ((b2 : ℝ) * (1 - (b1 : ℝ) / (m : ℝ))) ≤ G.gameValue b1 b2) := by sorry

end NetInspect.Rate
