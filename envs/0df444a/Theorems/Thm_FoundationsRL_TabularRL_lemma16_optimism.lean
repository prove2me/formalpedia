-- Prove2me | Theorems.Thm_FoundationsRL_TabularRL_lemma16_optimism
-- name    : FoundationsRL.TabularRL.lemma16_optimism
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:32.815666+00:00
-- url     : https://prove2.me/theorems/4130d10d-078e-4f30-954f-725a1fcc610c
-- title:
--   Lemma 16 — bonuses that dominate the error on $V^{M,\star}_{h+1}$ make $\bar Q_h$ optimistic (corrected: $V^{M,\star}_h\in[0,1]$ at every layer)
-- statement:
--   Let $M$ be a finite-horizon episodic MDP with finite state and action spaces, horizon $H$ and known rewards $r_h(s,a)\in[0,1]$, and assume $V^{M,\star}_h(s)\in[0,1]$ for every layer $h\in[H]$ and state $s$ (Assumption 6, corrected). Let $\widehat P_h(\cdot\mid s,a)$ be probability distributions on the state space and $b_{h,\delta}:\mathcal S\times\mathcal A\to\mathbb R$ functions such that, for all $h\in[H]$, $s$ and $a$,
--
--   $$
--   \Big|\sum_{s'}\widehat P_h(s'\mid s,a)V^{M,\star}_{h+1}(s')-\sum_{s'}P^M_h(s'\mid s,a)V^{M,\star}_{h+1}(s')\Big|\le b_{h,\delta}(s,a).
--   $$
--
--   Then the optimistic value functions $\bar Q_h,\bar V_h$ of (5.29), built from $\widehat P$ and $b$, satisfy for all $h\in[H]$
--
--   $$
--   \bar Q_h\ge Q^{M,\star}_h\quad\text{and}\quad \bar V_h\ge V^{M,\star}_h
--   $$
--
--   pointwise.
--
--   This is the optimism step of the UCB-VI analysis: once the bonuses cover the estimation error on the optimal value function, the clipped value-iteration estimates over-estimate the optimal values at every layer, which is the hypothesis of Lemma 15.
--
--   **Formalization Note** Layers are $0$-indexed; $Q^{M,\star}$, $V^{M,\star}$ are the published suprema over randomized non-stationary policies.
--
--   Differences from the source:
--
--   - correction: Assumption 6 (p. 89) bounds only the initial value, $V^{M,\star}_1(s)\in[0,1]$ → $V^{M,\star}_h(s)\in[0,1]$ for every layer $h\in[H]$ and state $s$; reason: the printed lemma is false: take $H=3$, states $u,z$, one action; layer 1 sends every state to $z$ with reward 0, layer 2 keeps $u\to u$ with reward 1 and $z\to z$ with reward 0, layer 3 gives reward 1 at $u$. Then $V^{M,\star}_1\equiv0$ satisfies Assumption 6, but $Q^{M,\star}_2(u,a)=2$, while with $\widehat P=P$ and $b\equiv0$ (so (5.30) holds) the clipped $\bar Q_2(u,a)=1$
--   - reading: (5.30) prints $V^{M,\star}_h(s')$ for the next state of a layer-$h$ transition → $V^{M,\star}_{h+1}(s')$; reason: misprint; the proof of Lemma 16 uses $V^{M,\star}_{h+1}$, and with $V^{M,\star}_h$ the hypothesis does not concern the quantity the induction needs
--   - encoding: layers $h=1,\dots,H$, $\bar Q_{H+1}\equiv0$ → layers $0,\dots,H-1$, `optQ` $=0$ from layer $H$ on; reason: Lean convention of the published `FoundationsRL_RLBasics_Core`; same instances
--   - encoding: estimates $\widehat P_h(\cdot\mid s,a)$ used as distributions ($s'\sim\widehat P_h$) → nonnegative vectors summing to 1 at every layer $h<H$; reason: the expectation in (5.28) presupposes a probability distribution; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 16, Eqs. (5.30)–(5.31), p. 91; Assumption 6, p. 89; Eq. (5.29), p. 90

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_TabularRL_optQ

namespace FoundationsRL.TabularRL

open FoundationsRL.RLBasics

/-- **Lemma 16** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, Lemma 16, Eqs. (5.30)–(5.31), p. 91): if the bonus
`b_{h,δ}(s,a)` dominates the error of the estimated transitions `P̂_h(·∣s,a)` on the optimal
next-layer value function `V^{M,⋆}_{h+1}`, then the value functions `Q̄_h`, `V̄_h` of (5.29)
are optimistic: `Q̄_h ≥ Q^{M,⋆}_h` and `V̄_h ≥ V^{M,⋆}_h` for every layer `h ∈ [H]`.

Standing assumptions of §5.6 (Assumption 6, p. 89, corrected): known rewards `r_h = R^M_h`
with values in `[0,1]`, and `V^{M,⋆}_h(s) ∈ [0,1]` for **every** layer `h ∈ [H]`.

**Formalization Note.** Layers are `0`-indexed (`h < H` is the book's `h + 1 ∈ [H]`).
Corrections and readings: (i) Assumption 6 as printed bounds only `V^{M,⋆}_1`; the proof's step
"if `Q̄_h(s,a) = 1` then trivially `Q̄_h(s,a) ≥ Q^{M,⋆}_h(s,a)`" needs `Q^{M,⋆}_h ≤ 1` at every
layer, and the lemma is false without it, so the bound is assumed at every layer. (ii) (5.30)
prints `V^{M,⋆}_h(s')` for a next state of a layer-`h` transition; the proof uses
`V^{M,⋆}_{h+1}`, which is what is stated. `P̂_h(·∣s,a)` is a probability vector on `S`, as the
expectation `E_{s'∼P̂_h(·∣s,a)}` in (5.28) requires. -/
theorem lemma16_optimism {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
    [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1)
    (hV : ∀ h, h < H → ∀ s, 0 ≤ Vstar M h s ∧ Vstar M h s ≤ 1)
    (Phat : ℕ → S → A → S → ℝ) (hPhat_nonneg : ∀ h, h < H → ∀ s a s', 0 ≤ Phat h s a s')
    (hPhat_sum : ∀ h, h < H → ∀ s a, ∑ s' : S, Phat h s a s' = 1)
    (b : ℕ → S → A → ℝ)
    (hb : ∀ h, h < H → ∀ s a,
      |∑ s' : S, Phat h s a s' * Vstar M (h + 1) s' - ∑ s' : S, M.P h s a s' * Vstar M (h + 1) s'|
        ≤ b h s a) :
    ∀ h, h < H →
      (∀ s a, Qstar M h s a ≤ optQ H M.R Phat b h s a) ∧
      (∀ s, Vstar M h s ≤ ⨆ a : A, optQ H M.R Phat b h s a) := by sorry

end FoundationsRL.TabularRL
