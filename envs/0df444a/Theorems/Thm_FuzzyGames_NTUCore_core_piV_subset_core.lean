-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_core_piV_subset_core
-- name    : FuzzyGames.NTUCore.core_piV_subset_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:13.44524+00:00
-- url     : https://prove2.me/theorems/a1642d35-00c3-4a65-9193-5284ce6a4618
-- title:
--   §7, p. 9 — if V(N) = πV(τ^N), the core of the fuzzy game πV is contained in the core of V
-- statement:
--   Let $\mathcal{C}$ be a family of nonempty coalitions of $N = \{1,\dots,n\}$ containing $N$ and every singleton, and let $V$ be a game without side payments on $\mathcal{C}$: for every $A \in \mathcal{C}$, $V(A)$ is a nonempty, closed, convex subset of $\mathbb{R}^A$ that is comprehensive and bounded above (§7 (1)). Its fuzzy extension is
--   $$\pi V(\tau) = \bigcup_{m \in \mathcal{C}(\tau)} \sum_{A \in \mathcal{C}} m(A)\, V(A),$$
--   where $\mathcal{C}(\tau)$ is the set of nonnegative weights $m$ on $\mathcal{C}$ with $\sum_{A \ni i} m(A) = \tau_i$ for every player $i$ (§6 (3)–(4), §7 (5)). Assume
--   $$V(N) = \pi V(\tau^N). \tag{8}$$
--   Then the core of the fuzzy game $\pi V$ (the $c\in\pi V(\tau^N)$ that no fuzzy coalition $\tau\neq 0$ improves upon) is contained in the core of $V$ (the $c \in V(N)$ with $\tau^A\cdot c\notin V(A)-\mathring{\mathbb{R}}^A_+$ for every $A\in\mathcal{C}$).
--
--   With Theorem 5.1 this gives the nonemptiness of the core of $V$ in Theorem 7.1.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §7, p. 9, sentence before (8)

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- §7, p. 9, sentence before (8): if `V(N) = πV(τ^N)`, the core of the fuzzy game `πV` is
contained in the core of the game `V`. -/
theorem core_piV_subset_core {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (hbal : V Finset.univ = piV 𝒞 V (coal Finset.univ)) :
    fuzzyCore (piV 𝒞 V) ⊆ ntuCore 𝒞 V := by sorry

end FuzzyGames.NTUCore
