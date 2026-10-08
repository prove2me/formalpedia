-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_eq_7_6
-- name    : FuzzyGames.NTUCore.eq_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:03:55.502597+00:00
-- url     : https://prove2.me/theorems/d15c9af0-bdc8-40d2-9ea4-bf83d7e81082
-- title:
--   §7 (6) — V(A) ⊆ πV(τ^A) for every A ∈ 𝒞
-- statement:
--   Let $\mathcal{C}$ be a family of nonempty coalitions of $N = \{1,\dots,n\}$ containing $N$ and every singleton, and let $V$ be a game without side payments on $\mathcal{C}$: for every $A \in \mathcal{C}$, $V(A)$ is a nonempty, closed, convex subset of $\mathbb{R}^A$ that is comprehensive and bounded above (§7 (1)). Its fuzzy extension is
--   $$\pi V(\tau) = \bigcup_{m \in \mathcal{C}(\tau)} \sum_{A \in \mathcal{C}} m(A)\, V(A),$$
--   where $\mathcal{C}(\tau)$ is the set of nonnegative weights $m$ on $\mathcal{C}$ with $\sum_{A \ni i} m(A) = \tau_i$ for every player $i$ (§6 (3)–(4), §7 (5)). Then
--   $$V(A)\subseteq \pi V(\tau^A)\qquad\text{for every } A\in\mathcal{C}.$$
--
--   It shows that $\pi V$ extends $V$ from the coalitions of $\mathcal{C}$ to all fuzzy coalitions without losing any payoff.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §7 (6), p. 9

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- §7 (6), p. 9: `V(A) ⊆ πV(τ^A)` for every `A ∈ 𝒞`. -/
theorem eq_7_6 {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) :
    ∀ A ∈ 𝒞.C, V A ⊆ piV 𝒞 V (coal A) := by sorry

end FuzzyGames.NTUCore
