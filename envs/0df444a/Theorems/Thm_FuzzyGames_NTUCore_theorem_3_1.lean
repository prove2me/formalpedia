-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_theorem_3_1
-- name    : FuzzyGames.NTUCore.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:03:46.946497+00:00
-- url     : https://prove2.me/theorems/3cdefc58-d505-459a-97e6-79e114a06c39
-- title:
--   Theorem 3.1 — strong canonical cooperative equilibria lie in the core; under (9) the core lies in the weak ones
-- statement:
--   Let $V$ be a fuzzy game without side payments: for every $\tau \in \mathbb{R}^n_+$, $V(\tau)$ is a nonempty, closed, convex subset of $\mathbb{R}^\tau$, comprehensive and bounded above, and $V(t\tau) = tV(\tau)$ for $t > 0$ (§3 (3)). Then:
--
--   1. every strong canonical cooperative equilibrium of $V$ belongs to the core of $V$;
--   2. if moreover $V$ satisfies
--   $$V(\tau+\sigma) \supseteq V(\tau)+V(\sigma)\qquad\text{for all } \tau,\sigma\in\mathbb{R}^n_+ \tag{9}$$
--   and $n \ge 1$, then the core of $V$ is contained in the set of weak canonical cooperative equilibria.
--
--   Here $c \in V(\tau^N)$ is a weak (resp. strong) canonical cooperative equilibrium if some $\bar\lambda$ in the simplex $M^n$ (resp. with all $\bar\lambda^i > 0$) satisfies $\sum_i\bar\lambda^i\tau_i c_i \ge v(\tau,\bar\lambda)$ for every $\tau\in[0,1]^n$.
--
--   The theorem sandwiches the core between the two kinds of equilibria; the minisup argument behind (b) is what later makes Theorem 5.1's "and thus" step work.
--
--   **Formalization Note.** The paper prints (9) as "$\tau,\sigma \subset \mathbb{R}^n_+$", a misprint for $\tau,\sigma\in\mathbb{R}^n_+$ (as §5 (1) prints it). The paper leaves $n \ge 1$ implicit; for $n = 0$ the simplex $M^n$ is empty while the core is not, so part (b) carries the hypothesis $0 < n$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Theorem 3.1 and (9), p. 5

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- Theorem 3.1 (§3, p. 5): (a) every strong canonical cooperative equilibrium is in the core;
(b) under superadditivity (9) (and `n ≥ 1`), the core is contained in the set of weak canonical
cooperative equilibria. -/
theorem theorem_3_1 {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)} (hV : IsNTUFuzzyGame V) :
    strongCCE V ⊆ fuzzyCore V ∧
      (Superadditive V → 0 < n → fuzzyCore V ⊆ weakCCE V) := by sorry

end FuzzyGames.NTUCore
