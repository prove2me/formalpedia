-- Prove2me | Theorems.Thm_FuzzyGames_TUCore_proposition_6_1
-- name    : FuzzyGames.TUCore.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:48.420979+00:00
-- url     : https://prove2.me/theorems/41ef776f-5eee-41cd-9c0d-e98cbc76b1d4
-- title:
--   Proposition 6.1 — the core of a game with side payments is nonempty iff the game is balanced, and then it is the core of $\pi v$
-- statement:
--   Let $N=\{1,\dots,n\}$, let $\mathscr C$ be a family of nonempty coalitions containing $N$ and every singleton $\{i\}$, and let $v:\mathscr C\to\mathbb R$ be a game with side payments. Its core is the set of $c\in\mathbb R^n$ with $\sum_{i\in N}c_i=v(N)$ and $\sum_{i\in A}c_i\ge v(A)$ for every $A\in\mathscr C$. Let
--   $$\pi v(\tau)=\sup\Big\{\sum_{A\in\mathscr C}m(A)v(A):\ m(A)\ge0,\ \ \sum_{A\in\mathscr C,\,A\ni i}m(A)=\tau_i\ (i\in N)\Big\}\qquad(\tau\in\mathbb R^n_+),$$
--   and call $v$ balanced if $\pi v(\tau^N)=v(N)$. Then
--
--   1. the core of $v$ is nonempty if and only if $v$ is balanced;
--   2. if $v$ is balanced, the core of $v$ coincides with the core of the fuzzy game $\pi v$:
--   $$\operatorname{core}(v)=\Big\{c\in\mathbb R^n:\ \sum_{i\in N}c_i=\pi v(\tau^N),\ \ \sum_{i\in N}\tau_ic_i\ge\pi v(\tau)\ \text{ for all }\tau\in[0,1]^n\Big\}.$$
--
--   This is the Bondareva–Shapley theorem, phrased through the concave positively homogeneous extension $\pi v$: the usual game inherits a nonempty core exactly when extending it to fuzzy coalitions does not raise the worth of the grand coalition.
--
--   **Formalization Note** Balancedness is the equation $\pi v(\tau^N)=v(N)$ with $\pi v$ computed from the balances of §6 (3)–(4); it is not defined through the core. The family $\mathscr C$ is general (not necessarily all nonempty coalitions) and both the core and $\pi v$ use only coalitions in $\mathscr C$. "In this case" is read as "if $v$ is balanced", which by the first part is the same as "if the core is nonempty".
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Proposition 6.1, p. 8

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

namespace FuzzyGames.TUCore

theorem proposition_6_1 {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (v : Finset (Fin n) → ℝ) :
    ((core 𝒞 v).Nonempty ↔ IsBalanced 𝒞 v) ∧
      (IsBalanced 𝒞 v → core 𝒞 v = fuzzyCore (piV 𝒞 v)) := by sorry

end FuzzyGames.TUCore
