-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_proposition_3_1
-- name    : FuzzyGames.NTUCore.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:03:22.935018+00:00
-- url     : https://prove2.me/theorems/3039f6a3-2283-4b35-93d5-279d5a5a3251
-- title:
--   Proposition 3.1 — c is in the core of a fuzzy game without side payments iff its maximum complaint α(c) is ≤ 0
-- statement:
--   Let $V$ be a fuzzy game without side payments: for every $\tau \in \mathbb{R}^n_+$, $V(\tau)$ is a nonempty, closed, convex subset of $\mathbb{R}^\tau$, comprehensive and bounded above, and $V(t\tau) = tV(\tau)$ for $t > 0$ (§3 (3)). Write $v(\tau,\lambda) = \sup_{c\in V(\tau)}\sum_i\lambda_i c_i$ for its support function and $M^\tau$ for the set of $\lambda \ge 0$ supported on $A_\tau = \{i : \tau_i > 0\}$ with $\sum_i \lambda^i = 1$. Let $c \in V(\tau^N)$ and define the maximum complaint
--   $$\alpha(c) = \sup_{\tau\in[0,1]^n,\ \tau\neq 0}\ \inf_{\lambda\in M^\tau}\Big[v(\tau,\lambda) - \sum_{i\in N}\lambda^i\tau_i c_i\Big].$$
--   Then $c$ belongs to the core of $V$ (no fuzzy coalition $\tau \neq 0$ has $\tau\cdot c \in V(\tau) - \mathring{\mathbb{R}}^\tau_+$) if and only if
--   $$\alpha(c) \le 0.$$
--
--   The proposition turns the blocking condition, one set-membership test per fuzzy coalition, into a single scalar inequality through support functions; Theorem 3.1 is derived from it.
--
--   **Formalization Note.** $\alpha(c)$ is computed in `EReal`. The paper takes the supremum over all $\tau\in[0,1]^n$; at $\tau = 0$ the set $M^0$ is empty and the inner infimum is $+\infty$, so we take it over $\tau \neq 0$, matching the core's quantifier.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Proposition 3.1 and (7), p. 4

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- Proposition 3.1 (§3, p. 4): for `c ∈ V(τ^N)`, `c` is in the core iff `α(c) ≤ 0`. -/
theorem proposition_3_1 {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)} (hV : IsNTUFuzzyGame V)
    {c : Fin n → ℝ} (hc : c ∈ V (coal Finset.univ)) :
    c ∈ fuzzyCore V ↔ maxComplaint V c ≤ 0 := by sorry

end FuzzyGames.NTUCore
