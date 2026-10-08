-- Prove2me | Theorems.Thm_FuzzyGames_TUCore_balances_support
-- name    : FuzzyGames.TUCore.balances_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:27.406986+00:00
-- url     : https://prove2.me/theorems/73ebfb9d-ff26-48c6-ac7b-b971e2e7fd04
-- title:
--   §6 (5) — a coalition with positive weight in $\mathscr C(\tau)$ lies in the support of $\tau$
-- statement:
--   Let $\mathscr C$ be a family of nonempty coalitions containing $N$ and every singleton, let $\tau\in\mathbb R^n$ and let $m\in\mathscr C(\tau)$, i.e. $m(A)\ge0$, $m$ vanishes off $\mathscr C$ and $\tau_i=\sum_{A\ni i}m(A)$ for every $i\in N$. Then for every coalition $A$,
--   $$m(A)>0\ \Longrightarrow\ A\subseteq A_\tau=\{i\in N:\ \tau_i>0\}.$$
--
--   Only players who actually participate in the fuzzy coalition $\tau$ can belong to a coalition used with positive weight to decompose $\tau$.
--
--   **Formalization Note** The paper considers $\tau$ a fuzzy coalition; the statement is made for every $\tau\in\mathbb R^n$, which contains the paper's case.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §6, (5), p. 8

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

namespace FuzzyGames.TUCore

theorem balances_support {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (τ : Fin n → ℝ)
    (m : Finset (Fin n) → ℝ) (hm : m ∈ FuzzyGames.NTUCore.balances 𝒞 τ) (A : Finset (Fin n)) (hA : 0 < m A) :
    A ⊆ Finset.univ.filter (fun i => 0 < τ i) := by sorry

end FuzzyGames.TUCore
