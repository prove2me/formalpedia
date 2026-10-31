-- Prove2me | Theorems.Thm_GoTBandit_Main_lemma_IV_2
-- name    : GoTBandit.Main.lemma_IV_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:40.468506+00:00
-- url     : https://prove2.me/theorems/fcd45e80-daf6-4652-b242-0f6bf35b4216
-- title:
--   Lemma IV.2, p. 7 — an estimation error below (J1 − J2)/(2N) keeps every estimated optimal assignment optimal
-- statement:
--   Let $N\le M$ and let $\mu=(\mu_{n,i})$ be positive mean rewards, with optimal objective $J_1$ and second best objective $J_2$ (the largest objective value strictly below $J_1$). Let $\hat\mu=(\hat\mu_{n,i})$ satisfy $|\hat\mu_{n,i}-\mu_{n,i}|<\Delta$ for every $n$ and $i$. If
--
--   $$
--   \Delta\le\frac{J_1-J_2}{2N},
--   $$
--
--   then
--
--   $$
--   \arg\max_a\sum_{n=1}^Ng_n(a)\supseteq\arg\max_a\sum_{n=1}^N\hat\mu_{n,a_n}\eta_{a_n}(a),
--   $$
--
--   where $g_n(a)=\mu_{n,a_n}\eta_{a_n}(a)$: every assignment that is optimal for the estimates is optimal for the true means.
--
--   This is the deterministic step that turns accurate estimates into a correct assignment in the analysis of the exploration phase.
--
--   **Formalization Note** The positivity of the means and $M\ge N$ are the standing assumptions of §II. If every profile has the optimal objective, $J_2$ takes the junk value $0$, and the conclusion holds trivially because every profile is optimal.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, p. 7, Lemma IV.2, Eq. (16)

import Mathlib
import Definitions.Def_GoTBandit_Main_Assignment

namespace GoTBandit.Main

/-- Lemma IV.2, p. 7, Eq. (16): if every mean is known up to an error `< Δ` with
`Δ ≤ (J1 − J2)/(2N)`, every optimal assignment for the estimates is optimal for the true
means. -/
theorem lemma_IV_2 {N M : ℕ} (hNM : N ≤ M) (μ μhat : Fin N → Fin M → ℝ)
    (hμ : ∀ n i, 0 < μ n i) (Δ : ℝ) (hest : ∀ n i, |μhat n i - μ n i| < Δ)
    (hΔ : Δ ≤ (J1 μ - J2 μ) / (2 * N)) :
    {a | IsOptimal μhat a} ⊆ {a | IsOptimal μ a} := by sorry

end GoTBandit.Main
