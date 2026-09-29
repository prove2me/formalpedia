-- Prove2me | Theorems.Thm_NonmonotoneSubmod_LocalSearch_approx_local_opt_vs_any_set
-- name    : NonmonotoneSubmod.LocalSearch.approx_local_opt_vs_any_set
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:04:18.150992+00:00
-- url     : https://prove2.me/theorems/e271a053-639f-4e6c-ac4e-709e506f69a0
-- title:
--   §3.1, proof of Theorem 3.4, first display — $2(1+n\alpha)f(S) + f(X\setminus S) \ge f(C)$
-- statement:
--   Let $f : 2^X \to \mathbb{R}_{\ge 0}$ be a nonnegative submodular function on a finite ground set $X$ with $n = |X|$ elements, let $\alpha \ge 0$, and let $S$ be a $(1+\alpha)$-approximate local optimum of $f$. Then for every set $C \subseteq X$,
--
--   $$2(1 + n\alpha)\, f(S) + f(X \setminus S) \ge f(C).$$
--
--   Taking $C$ optimal, one of $f(S)$ and $f(X \setminus S)$ is at least $\mathrm{OPT}/(3 + 2n\alpha)$, which is the $1/3$ guarantee of Algorithm LS.
--
--   **Formalization Note** The paper takes $C$ to be an optimal solution; the inequality holds for every $C$ and is stated so. Nonnegativity of $f$ is the standing assumption of §3; $\alpha \ge 0$ is needed for Lemma 3.3.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1141, §3.1, proof of Theorem 3.4, first display

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

/-- Feige–Mirrokni–Vondrák 2011, §3.1, proof of Theorem 3.4, p. 1141, first display: for a
nonnegative submodular `f`, `α ≥ 0`, a `(1 + α)`-approximate local optimum `S` and any set `C`,
`2(1 + nα) f(S) + f(X \ S) ≥ f(C)`, where `n = |X|`. -/
theorem approx_local_opt_vs_any_set {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (C : Finset X) :
    f C ≤ 2 * (1 + (Fintype.card X : ℝ) * α) * f S + f Sᶜ := by sorry

end NonmonotoneSubmod.LocalSearch
