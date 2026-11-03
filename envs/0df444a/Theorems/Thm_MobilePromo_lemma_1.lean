-- Prove2me | Theorems.Thm_MobilePromo_lemma_1
-- name    : MobilePromo.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:46.782147+00:00
-- url     : https://prove2.me/theorems/9e1ac678-ad11-4398-93fe-1fc04846c449
-- title:
--   Lemma 1: the optimal bids are Lipschitz in $\gamma$ with constant $K_1^T$
-- statement:
--   Under Assumptions 1 and 3 there is a constant $K_1>1$, independent of $I$ and $T$, such that for all $l$, all $\gamma,\hat\gamma\in\Gamma^{(0)}$, all seasons $1\le i\le I$, all $1\le t\le T$ and all states with $\mathcal F\ne\emptyset$,
--
--   $$
--   \bigl|b^*_{i,t,l}(\boldsymbol c_i;\gamma)-b^*_{i,t,l}(\boldsymbol c_i;\hat\gamma)\bigr|\le K_1^T\|\gamma-\hat\gamma\| .
--   $$
--
--   This compares the bid computed from an estimate with the one computed from the true parameter.
--
--   Differences from the source:
--   - reading: "For all $l$, $\gamma,\hat\gamma$, $\mathcal F\ne\emptyset$, $i$, $t$, there exists a constant $K_1>1$ that is independent of $I$ and $T$" → $K_1$ is chosen first, before all of these; reason: the proof fixes $K_1=\max\{2\max_lK_8^l,2K_9+1\}$ at the end; with the printed word order the lemma would be trivial
--   - generalization: constants "independent of $I$ and $T$" → the constants are also chosen before the schedule, the true parameter and the choice among likelihood maximizers; reason: the schedule varies with $I$, so the constants must not see it; the printed proof gives this (compactness of $[b^{\min}-e,0]\times\Gamma^{(0)}\times B$), and it specializes to the printed claim
--   - encoding: states with $\mathcal F\ne\emptyset$ → states $\boldsymbol c\le\boldsymbol W$ with $\mathcal F\ne\emptyset$; reason: the state space of p.8
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
--   - encoding: the $I$ seasons of $C_I$ (p.7) → `Schedule T := ℕ → Season T`, of which only the first $I$ are read; reason: the regret, Assumption 3 and the first $IT$ periods of BidAlloc see only seasons $0,\dots,I-1$, and a finite schedule extends; no instance changes
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Lemma 1, p.14; proof A5–A6 (PDF 39–40)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_Assumption3

set_option autoImplicit false

namespace MobilePromo

/-- Lemma 1 (SSRN 3523491, Lemma 1, p.14): there is `K₁ > 1`, independent of `I` and `T`, with
`|b*_{i,t,l}(c; γ) - b*_{i,t,l}(c; γ̂)| ≤ K₁^T ‖γ - γ̂‖` for all `l`, `γ, γ̂ ∈ Γ⁽⁰⁾`, `F ≠ ∅`, `1 ≤ i ≤ I`,
`1 ≤ t ≤ T`.

**Formalization Note** `K₁` comes first, as the proof gives it (A6). It also does not see the schedule. -/
theorem lemma_1 (M : Model) (h1 : Assumption1 M) :
    ∃ K₁ : ℝ, 1 < K₁ ∧ ∀ {T : ℕ} (S : Schedule T) (I : ℕ), Assumption3 M S I →
      ∀ i < I, ∀ t, 1 ≤ t → t ≤ T → ∀ c : Fin (S i).m → ℕ, c ≤ (S i).W →
        ((S i).activeSet t c).Nonempty → ∀ l, ∀ γ ∈ M.Gamma0, ∀ γ' ∈ M.Gamma0,
          |bStar M (S i) γ t c l - bStar M (S i) γ' t c l| ≤ K₁ ^ T * ‖γ - γ'‖ := by sorry

end MobilePromo
