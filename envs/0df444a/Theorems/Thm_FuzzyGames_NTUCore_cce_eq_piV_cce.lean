-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_cce_eq_piV_cce
-- name    : FuzzyGames.NTUCore.cce_eq_piV_cce
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:25.159058+00:00
-- url     : https://prove2.me/theorems/d68b744a-84c5-465a-8aa2-1d6b78642f74
-- title:
--   §7, proof of Theorem 7.1 — for a balanced game the canonical cooperative equilibria of V and of πV coincide
-- statement:
--   Let $\mathcal{C}$ be a family of nonempty coalitions of $N = \{1,\dots,n\}$ containing $N$ and every singleton, and let $V$ be a game without side payments on $\mathcal{C}$: for every $A \in \mathcal{C}$, $V(A)$ is a nonempty, closed, convex subset of $\mathbb{R}^A$ that is comprehensive and bounded above (§7 (1)). Its fuzzy extension is
--   $$\pi V(\tau) = \bigcup_{m \in \mathcal{C}(\tau)} \sum_{A \in \mathcal{C}} m(A)\, V(A),$$
--   where $\mathcal{C}(\tau)$ is the set of nonnegative weights $m$ on $\mathcal{C}$ with $\sum_{A \ni i} m(A) = \tau_i$ for every player $i$ (§6 (3)–(4), §7 (5)). Assume $V$ is balanced, $V(N) = \pi V(\tau^N)$. Then
--
--   1. the weak canonical cooperative equilibria of the game $V$ (§7 (3)) coincide with the weak canonical cooperative equilibria of the fuzzy game $\pi V$ (§3 (8));
--   2. the strong canonical cooperative equilibria of $V$ coincide with the strong canonical cooperative equilibria of $\pi V$.
--
--   This is the fact the proof of Theorem 7.1 combines with Theorem 3.1.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §7, proof of Theorem 7.1, pp. 9–10

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- §7, proof of Theorem 7.1 (pp. 9–10): for a balanced game, the weak (resp. strong) canonical
cooperative equilibria of the game `V` and of the fuzzy game `πV` coincide. -/
theorem cce_eq_piV_cce {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (hbal : IsBalanced 𝒞 V) :
    ntuWeakCCE 𝒞 V = weakCCE (piV 𝒞 V) ∧ ntuStrongCCE 𝒞 V = strongCCE (piV 𝒞 V) := by sorry

end FuzzyGames.NTUCore
