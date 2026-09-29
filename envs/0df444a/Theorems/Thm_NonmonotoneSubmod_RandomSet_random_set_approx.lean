-- Prove2me | Theorems.Thm_NonmonotoneSubmod_RandomSet_random_set_approx
-- name    : NonmonotoneSubmod.RandomSet.random_set_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:00:23.992134+00:00
-- url     : https://prove2.me/theorems/c8f5152a-1ce0-4976-8894-6238f65344e9
-- title:
--   Theorem 2.1 — a uniformly random set achieves $\frac14 OPT$, and $\frac12 OPT$ for symmetric $f$
-- statement:
--   Let $X$ be a finite ground set and $f : 2^X \to \mathbb{R}_+$ a nonnegative submodular function. Let $OPT = \max_{S \subseteq X} f(S)$, and let $R = X(1/2)$ be a uniformly random subset of $X$, containing each element independently with probability $\tfrac12$. Then
--
--   $$\mathbf{E}[f(R)] \ge \tfrac14\, OPT.$$
--
--   In addition, if $f$ is symmetric, i.e. $f(X \setminus S) = f(S)$ for every $S \subseteq X$, then
--
--   $$\mathbf{E}[f(R)] \ge \tfrac12\, OPT.$$
--
--   Hence Algorithm RS, which returns $X(1/2)$ without querying $f$ at all, is a $\tfrac14$-approximation for maximizing nonnegative submodular functions and a $\tfrac12$-approximation for symmetric ones. This generalizes the classical random-cut guarantees for Max Di-Cut ($\tfrac14$) and Max Cut ($\tfrac12$).
--
--   **Formalization Note** $\mathbf{E}[f(R)]$ is the multilinear extension $F$ at the constant vector $\tfrac12$, i.e. $2^{-|X|} \sum_{S \subseteq X} f(S)$; $OPT$ is the maximum over the finite nonempty family of all subsets of $X$. Nonnegativity is the hypothesis $f(S) \ge 0$ for all $S$ on a real-valued $f$. Both parts are stated in one theorem, the second under the symmetry hypothesis. $X$ may be empty; the statement is then still meaningful and true.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Theorem 2.1 (proof p. 1138)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.RandomSet

/-- Theorem 2.1 (Feige–Mirrokni–Vondrák 2011, p. 1137). Let `f : 2^X → ℝ₊` be a nonnegative
submodular function on a finite ground set `X`, let `OPT = max_{S ⊆ X} f(S)`, and let
`R = X(1/2)` be a uniformly random subset of `X`. Then `E[f(R)] ≥ ¼ OPT`; if in addition `f` is
symmetric (`f(X \ S) = f(S)` for every `S`), then `E[f(R)] ≥ ½ OPT`. -/
theorem random_set_approx {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    (1 / 4) * NonmonotoneSubmod.Shared.OPT f ≤ NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) ∧
      (NonmonotoneSubmod.Shared.SymmetricSetFun f → (1 / 2) * NonmonotoneSubmod.Shared.OPT f ≤ NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2)) := by sorry

end NonmonotoneSubmod.RandomSet
