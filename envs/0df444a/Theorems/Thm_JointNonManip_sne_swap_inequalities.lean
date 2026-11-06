-- Prove2me | Theorems.Thm_JointNonManip_sne_swap_inequalities
-- name    : JointNonManip.sne_swap_inequalities
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:30.324197+00:00
-- url     : https://prove2.me/theorems/92e3ec39-e915-44e2-af81-a1deb2e00400
-- title:
--   Definition 2.5, p.6 — every point of $S_{\mathrm{NE}}(G_{\mathcal L})$ satisfies every learner's swap-regret inequalities
-- statement:
--   Let $G$ be a finite game with nonempty action sets and learner utilities $u_i:A\to[-1,1]$, and let $S_{\mathrm{NE}}(G_{\mathcal L})$ be the Nash response target. Then for every $\mu\in S_{\mathrm{NE}}(G_{\mathcal L})$, every learner $i\in\mathcal L$ and every swap $\phi:A_i\to A_i$,
--   $$
--   G_{i,\phi}(\mu)=\sum_{a\in A}\mu(a)\,\big[u_i(a_0,\phi(a_i),a_{-i})-u_i(a)\big]\le 0 .
--   $$
--
--   This is the first of the two menu properties of Lemma 3.1: once the menu of the learners is $S_{\mathrm{NE}}$, no learner has swap regret.
--
--   Differences from the source:
--   - encoding: learners L = {1, …, n − 1}, finite action sets A₀, Aᵢ (a finite normal-form game, p.4) → a finite type L of learners (empty when n = 1) and finite nonempty types A0, Act i; reason: relabeling; ∆(Aᵢ) is empty unless Aᵢ is nonempty, so nonemptiness is part of the source's model
--   - encoding: CSPs µ ∈ ∆(A) ⊂ ℝ^A, y ⊗ q, ⟨·,·⟩, q = ⊗ᵢ xᵢ ∈ ∆(A_L), ℓ₁ and ℓ₂ norms → real functions on A0 × ((i : L) → Act i); otimes, pairing; AGT.profileProb x of a profile of lotteries AGT.IsLottery; explicit sums l1dist, l2dist; reason: Lean representation of the same objects
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Definition 2.5, closing sentence, p.6; p.8 ('By linearity, the same individual swap inequalities hold throughout SNE(GL)')

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Every point of `S_NE(G_L)` satisfies every learner's swap-regret inequalities**
(Collina, Fullerton, Liu & Weinberg, *Non-manipulability and Approachability Beyond Two-Player
Games*, manuscript (STOC 2027 submission), Definition 2.5, closing sentence, p.6; p.8, "By
linearity, the same individual swap inequalities hold throughout SNE(GL)").

For a finite game with nonempty action sets and learner utilities in `[−1, 1]` (p.4), every
`μ ∈ S_NE(G_L)`, every learner `i` and every swap `ϕ : Aᵢ → Aᵢ` satisfy `G_{i,ϕ}(μ) ≤ 0`. -/
theorem sne_swap_inequalities [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1) :
    ∀ μ ∈ SNE u, ∀ (i : L) (ϕ : Act i → Act i), swapGain u i ϕ μ ≤ 0 := by sorry

end JointNonManip
