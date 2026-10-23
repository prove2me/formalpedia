-- Prove2me | Theorems.Thm_GoTBandit_Main_theorem_III_1
-- name    : GoTBandit.Main.theorem_III_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:24.486478+00:00
-- url     : https://prove2.me/theorems/e77c1db1-bf54-438d-91a7-0696301dcd3f
-- title:
--   Theorem III.1, p. 5 — the Game of Thrones algorithm has expected total regret at most 4 µmax (c1 + c2) N log₂^{1+δ}(T/c3 + 2) for small ε and large T
-- statement:
--   Let $N\le M$ players face $M$ arms with i.i.d. rewards as in Definition II.1, with positive means $\mu_{n,i}$, such that the assignment problem $\max_a\sum_ng_n(a)$ of Eq. (4) has a unique solution $a^*$. Let every player run Algorithm 1 with integers $c_1,c_2,c_3>0$, $\delta>0$ and a GoT exponent $c>J_0-J_1$, where $J_1$ is the optimal objective and $J_0=\sum_n\max_a g_n(a)$. The horizon $T$ is unknown to the players. Then there is $\varepsilon\in(0,1)$ such that for all large enough $T$ the expected total regret satisfies
--
--   $$
--   \bar R\le4\Big(\max_{n,i}\mu_{n,i}\Big)(c_1+c_2)\,N\log_2^{1+\delta}\Big(\frac T{c_3}+2\Big).
--   $$
--
--   So, without any communication and with each player seeing only her own rewards, the players achieve a regret of order $O(\log^{1+\delta}T)$, within a $\log^\delta T$ factor of the $\Omega(\log T)$ lower bound.
--
--   **Formalization Note** The exponent $c$ of the GoT dynamics does not appear in Theorem III.1; the hypothesis $c>J_0-J_1$ on the true means is added (the dynamics of §III-A require $c\ge J_0-J_1$, and Theorem V.6 needs the strict inequality for each epoch's estimated utilities). The witness $\varepsilon$ is required to lie below $1$ so that the dynamics are probabilities; this does not weaken the statement. $\log_2^{1+\delta}x$ is $(\log_2x)^{1+\delta}$, and $T/c_3$ is real division. The trailing "$=O(\log^{1+\delta}T)$" of Eq. (9) is a gloss and is not formalized separately. The players' randomization is realized by private uniform seeds independent of the rewards; each player's rule reads only her own memory, seeds and received reward.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, p. 5, Theorem III.1, Eq. (9)

import Mathlib
import Definitions.Def_GoTBandit_Main_Algorithm

open Finset MeasureTheory ProbabilityTheory

namespace GoTBandit.Main

/-- Theorem III.1 (Main Theorem), p. 5, Eq. (9). Every player runs Algorithm 1 with parameters
`c1, c2, c3 ≥ 1`, `δ > 0`, GoT exponent `c > J0 − J1` (disclosed addition: `c` is not
mentioned in the theorem) and some `ε ∈ (0, 1)`; then for large enough `T` the expected total
regret is at most `4 (max_{n,i} μ_{n,i}) (c1 + c2) N log₂^{1+δ}(T/c3 + 2)`. -/
theorem theorem_III_1 {N M : ℕ} (hNM : N ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (aStar : Fin N → Fin M) (hopt : IsOptimal μ aStar)
    (huniq : ∀ a, IsOptimal μ a → a = aStar)
    (c1 c2 c3 : ℕ) (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3) (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : J0 μ - J1 μ < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      expRegret P ⟨c1, c2, c3, δ, ε, c⟩ hNM r ξ aStar T ≤
        4 * (⨆ n, ⨆ i, μ n i) * ((c1 : ℝ) + c2) * N *
          (Real.logb 2 ((T : ℝ) / c3 + 2)) ^ (1 + δ) := by sorry

end GoTBandit.Main
