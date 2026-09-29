-- Prove2me | Theorems.Thm_NonmonotoneSubmod_LocalSearch_opt_le_card_mul_max_singleton
-- name    : NonmonotoneSubmod.LocalSearch.opt_le_card_mul_max_singleton
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:05:31.024104+00:00
-- url     : https://prove2.me/theorems/9663b874-df63-4300-a4cc-345bfad45810
-- title:
--   §3.1, proof of Theorem 3.4, last paragraph — $\mathrm{OPT} \le n f(\{v\})$
-- statement:
--   Let $f : 2^X \to \mathbb{R}_{\ge 0}$ be a nonnegative submodular function on a finite ground set $X$ with $n = |X| \ge 2$ elements, and let $v \in X$ be a singleton of maximum value: $f(\{w\}) \le f(\{v\})$ for every $w \in X$. Then
--
--   $$\mathrm{OPT} = \max_{T \subseteq X} f(T) \le n\, f(\{v\}).$$
--
--   Together with the growth of $f$ along a run of Algorithm LS, this bounds the number of iterations of the algorithm.
--
--   **Formalization Note** The hypothesis $n \ge 2$ is added: for $n = 1$ the claim is false ($X = \{v\}$, $f(\emptyset) = 5$, $f(\{v\}) = 0$ is nonnegative and submodular). Nonnegativity of $f$ is the standing assumption of §3.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1141, §3.1, proof of Theorem 3.4, last paragraph ("It is simple to see that OPT ≤ nf({v})")

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

/-- Feige–Mirrokni–Vondrák 2011, §3.1, proof of Theorem 3.4, p. 1141, last paragraph:
`OPT ≤ n f({v})` for a singleton `{v}` of maximum value, for a nonnegative submodular `f` on a
ground set of `n = |X| ≥ 2` elements. -/
theorem opt_le_card_mul_max_singleton {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hn : 2 ≤ Fintype.card X) (v : X) (hv : IsMaxSingleton f v) :
    NonmonotoneSubmod.Shared.OPT f ≤ (Fintype.card X : ℝ) * f {v} := by sorry

end NonmonotoneSubmod.LocalSearch
