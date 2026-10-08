-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_theorem_7_1
-- name    : FuzzyGames.NTUCore.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:28.058661+00:00
-- url     : https://prove2.me/theorems/ca353c39-588e-4790-bed7-602bfd2bbbd3
-- title:
--   Theorem 7.1 — a balanced game without side payments has a nonempty core containing the nonempty core of its fuzzy extension πV
-- statement:
--   Let $\mathcal{C}$ be a family of nonempty coalitions of $N = \{1,\dots,n\}$ containing $N$ and every singleton, and let $V$ be a game without side payments on $\mathcal{C}$: for every $A \in \mathcal{C}$, $V(A)$ is a nonempty, closed, convex subset of $\mathbb{R}^A$ that is comprehensive and bounded above (§7 (1)). Its fuzzy extension is
--   $$\pi V(\tau) = \bigcup_{m \in \mathcal{C}(\tau)} \sum_{A \in \mathcal{C}} m(A)\, V(A),$$
--   where $\mathcal{C}(\tau)$ is the set of nonnegative weights $m$ on $\mathcal{C}$ with $\sum_{A \ni i} m(A) = \tau_i$ for every player $i$ (§6 (3)–(4), §7 (5)). Assume the game is balanced:
--   $$V(N) = \pi V(\tau^N).$$
--   Then
--
--   1. the core of $V$ is nonempty;
--   2. the core of the fuzzy game $\pi V$ is nonempty and contained in the core of $V$;
--   3. every strong canonical cooperative equilibrium of $V$ belongs to the core of $\pi V$;
--   4. the core of $\pi V$ is contained in the set of weak canonical cooperative equilibria of $V$.
--
--   The paper presents the result as a corollary of Scarf's theorem on the nonemptiness of the core of a balanced game without side payments, obtained here from the fuzzy-game Theorem 5.1.
--
--   **Formalization Note.** The core of $\pi V$ is the core of §3 (4) applied to the map $\tau\mapsto\pi V(\tau)$; the equilibria of $V$ are those of §7 (3)–(4). $\mathcal{C}$ excludes the empty coalition and contains $N$, which forces $n\ge 1$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Theorem 7.1, p. 9

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- Theorem 7.1 (§7, p. 9): for a balanced game without side payments, the core is nonempty and
contains the nonempty core of the fuzzy game `πV`; every strong canonical cooperative equilibrium
of `V` lies in the core of `πV`, which lies in the set of weak canonical cooperative equilibria
of `V`. -/
theorem theorem_7_1 {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) (hbal : IsBalanced 𝒞 V) :
    (ntuCore 𝒞 V).Nonempty ∧
      (fuzzyCore (piV 𝒞 V)).Nonempty ∧ fuzzyCore (piV 𝒞 V) ⊆ ntuCore 𝒞 V ∧
      ntuStrongCCE 𝒞 V ⊆ fuzzyCore (piV 𝒞 V) ∧
      fuzzyCore (piV 𝒞 V) ⊆ ntuWeakCCE 𝒞 V := by sorry

end FuzzyGames.NTUCore
