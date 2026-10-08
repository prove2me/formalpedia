-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_theorem_5_1
-- name    : FuzzyGames.NTUCore.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:03:44.453418+00:00
-- url     : https://prove2.me/theorems/cd965b1b-6fd0-4c6c-a66f-861131711092
-- title:
--   Theorem 5.1 — a superadditive fuzzy game without side payments has a nonempty core
-- statement:
--   Let $V$ be a fuzzy game without side payments: for every $\tau \in \mathbb{R}^n_+$, $V(\tau)$ is a nonempty, closed, convex subset of $\mathbb{R}^\tau$, comprehensive and bounded above, and $V(t\tau) = tV(\tau)$ for $t > 0$ (§3 (3)). Assume $n \ge 1$ and
--   $$V(\tau+\sigma)\supseteq V(\tau)+V(\sigma)\qquad\text{for all }\tau,\sigma\in\mathbb{R}^n_+. \tag{1}$$
--   Then the core of $V$ is nonempty, and hence weak canonical cooperative equilibria exist.
--
--   This is the core-existence theorem for fuzzy games without side payments; applied to the fuzzy extension $\pi V$ of a usual game it yields Scarf's theorem in Theorem 7.1.
--
--   **Formalization Note.** The conclusion is the conjunction of both claims of the paper's sentence: the core is nonempty, and the set of weak canonical cooperative equilibria is nonempty. The hypothesis $n\ge 1$ is implicit in the paper; for $n = 0$ there is no $\bar\lambda$ in the simplex.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Theorem 5.1 and (1), p. 6

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- Theorem 5.1 (§5, p. 6): a superadditive fuzzy game without side payments (with `n ≥ 1`)
has a nonempty core, and hence weak canonical cooperative equilibria exist. -/
theorem theorem_5_1 {n : ℕ} (hn : 0 < n) {V : (Fin n → ℝ) → Set (Fin n → ℝ)}
    (hV : IsNTUFuzzyGame V) (hsup : Superadditive V) :
    (fuzzyCore V).Nonempty ∧ (weakCCE V).Nonempty := by sorry

end FuzzyGames.NTUCore
