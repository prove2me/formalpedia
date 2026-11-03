-- Prove2me | Theorems.Thm_MobilePromo_eq_A4
-- name    : MobilePromo.eq_A4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:08.740357+00:00
-- url     : https://prove2.me/theorems/bef31897-a7ca-4d8a-8ba8-4eb92148ba28
-- title:
--   Inequality (A-4): $V_{i,t}$ is Lipschitz in $\gamma$ with constant at most $(2K_9+1)^{T-t+1}-1$
-- statement:
--   Under Assumption 1 there is $K_9>0$, independent of $T$ and of the season, such that for all $1\le t\le T+1$, all states $\boldsymbol c$ and all $\gamma,\hat\gamma\in\Gamma^{(0)}$,
--
--   $$
--   |V_{i,t}(\boldsymbol c;\gamma)-V_{i,t}(\boldsymbol c;\hat\gamma)|\le\bigl((2K_9+1)^{T-t+1}-1\bigr)\|\gamma-\hat\gamma\| .
--   $$
--
--   For $t\ge2$ this gives the printed $\kappa_t\le(2K_9+1)^{T-1}-1$. The exponential dependence on $T$ here is what produces the factor $K_1^{2T}$ in Theorem 1.
--
--   Differences from the source:
--   - generalization: $\kappa_t\le(2K_9+1)^{T-1}-1$ for $t\ge2$, in a section under Assumption 3 → the bound $(2K_9+1)^{T-t+1}-1$ of A6 for all $1\le t\le T+1$, without Assumption 3, for every state, with $K_9$ chosen before $T$ and the season; reason: this is the bound A6 proves, it implies the printed one, and the two inner minima can be compared with no differentiability
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, (A-4), A5 (PDF 39); derivation A6 (PDF 40)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

namespace MobilePromo

/-- Inequality (A-4) (SSRN 3523491, (A-4), A5–A6, PDF 39–40): `|V_{i,t}(c; γ) - V_{i,t}(c; γ̂)| ≤ κ_t ‖γ - γ̂‖`,
with the bound `κ_t ≤ (2K₉ + 1)^{T-t+1} - 1` proved on A6, for a `K₉ > 0` chosen before `T` and the season.

**Formalization Note** For `2 ≤ t` this implies the printed `κ_t ≤ (2K₉ + 1)^{T-1} - 1`. Assumption 3 is not
needed: the proof compares the two inner minima through `|min g - min ĝ| ≤ sup |g - ĝ|` on `B`, with `α`
in `[bmin - e, 0]` by Lemma A.2. `T + 1 - t` is exact because `t ≤ T + 1`. -/
theorem eq_A4 (M : Model) (h1 : Assumption1 M) :
    ∃ K₉ : ℝ, 0 < K₉ ∧ ∀ {T : ℕ} (S : Season T) (t : ℕ), 1 ≤ t → t ≤ T + 1 →
      ∀ (c : Fin S.m → ℕ), ∀ γ ∈ M.Gamma0, ∀ γ' ∈ M.Gamma0,
        |V M S γ t c - V M S γ' t c| ≤ ((2 * K₉ + 1) ^ (T + 1 - t) - 1) * ‖γ - γ'‖ := by sorry

end MobilePromo
