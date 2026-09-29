-- Prove2me | Theorems.Thm_NonmonotoneSubmod_RandomSet_uniform_four_corners
-- name    : NonmonotoneSubmod.RandomSet.uniform_four_corners
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:59:45.225373+00:00
-- url     : https://prove2.me/theorems/15e1cd5b-d1e9-49b2-997d-4d9f21f8dd2a
-- title:
--   Proof of Theorem 2.1, display — $\mathbf{E}[f(R)] \ge \frac14 f(\emptyset) + \frac14 f(S) + \frac14 f(\bar S) + \frac14 f(X)$
-- statement:
--   Let $X$ be a finite ground set, $f : 2^X \to \mathbb{R}$ submodular (of any sign), and let $R = X(1/2)$ be a uniformly random subset of $X$, containing each element independently with probability $\tfrac12$. For every $S \subseteq X$, with complement $\bar S = X \setminus S$,
--
--   $$\mathbf{E}[f(R)] \ge \tfrac14 f(\emptyset) + \tfrac14 f(S) + \tfrac14 f(\bar S) + \tfrac14 f(X).$$
--
--   This is the display in the proof of Theorem 2.1: writing $R = S(1/2) \cup \bar S(1/2)$ as the union of independent half-samples of $S$ and of $\bar S$ and applying Lemma 2.3 with $p = q = \tfrac12$. Theorem 2.1 follows from it by taking $S$ optimal and discarding the nonnegative terms.
--
--   **Formalization Note** $\mathbf{E}[f(R)]$ is the multilinear extension $F$ at the constant vector $\tfrac12$, i.e. $2^{-|X|} \sum_{S \subseteq X} f(S)$. The statement holds for every $S \subseteq X$; optimality of $S$ is used only in Theorem 2.1. The identity between $X(1/2)$ and $S(1/2) \cup \bar S(1/2)$ is part of what this statement asserts.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1138, §2, proof of Theorem 2.1, display

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.RandomSet

/-- Display in the proof of Theorem 2.1 (Feige–Mirrokni–Vondrák 2011, p. 1138). For a submodular
`f : 2^X → ℝ` and any `S ⊆ X`, the uniformly random subset `R = X(1/2) = S(1/2) ∪ S̄(1/2)` satisfies
`E[f(R)] ≥ ¼ f(∅) + ¼ f(S) + ¼ f(S̄) + ¼ f(X)`. -/
theorem uniform_four_corners {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) :
    (1 / 4) * f ∅ + (1 / 4) * f S + (1 / 4) * f Sᶜ + (1 / 4) * f Finset.univ ≤
      NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) := by sorry

end NonmonotoneSubmod.RandomSet
