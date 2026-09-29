-- Prove2me | Theorems.Thm_NonmonotoneSubmod_LocalSearch_lemma_3_3_approx_local_optimum
-- name    : NonmonotoneSubmod.LocalSearch.lemma_3_3_approx_local_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:02:40.214236+00:00
-- url     : https://prove2.me/theorems/a837b2a9-e482-47cd-b8b2-cc562bc8c5af
-- title:
--   Lemma 3.3 — an approximate local optimum nearly dominates its subsets and supersets
-- statement:
--   Let $f : 2^X \to \mathbb{R}_{\ge 0}$ be a nonnegative submodular function on a finite ground set $X$ with $n = |X|$ elements, let $\alpha \ge 0$, and let $S$ be a $(1+\alpha)$-approximate local optimum of $f$ (Definition 3.2). Then for every $T \subseteq X$ with $T \subseteq S$ or $T \supseteq S$,
--
--   $$f(T) \le (1 + n\alpha)\, f(S).$$
--
--   This is the approximate analogue of Lemma 3.1 and the only property of the output of Algorithm LS that the analysis of Theorem 3.4 uses.
--
--   **Formalization Note** Two hypotheses are made explicit. Nonnegativity of $f$ is the standing assumption of §3 of the paper ("maximizing a general nonnegative submodular function"); the lemma is false without it (take $X = \{v, w\}$, $f(X) = -1$, $f(\{v\}) = f(\{w\}) = -2$, $f(\emptyset) = -3$, $\alpha = 1$, $S = X$, $T = \{w\}$). The condition $\alpha \ge 0$ is not written on the page; it is needed to replace the chain length by $n$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1141, Lemma 3.3 (with the §3 standing assumption f ≥ 0, p. 1140)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

/-- Lemma 3.3 (Feige–Mirrokni–Vondrák 2011, p. 1141), under the standing assumption of §3 that `f`
is nonnegative: if `S` is a `(1 + α)`-approximate local optimum of a nonnegative submodular `f`
with `α ≥ 0`, then `f(T) ≤ (1 + nα) f(S)` for every `T` with `T ⊆ S` or `T ⊇ S`, where
`n = |X|`. -/
theorem lemma_3_3_approx_local_optimum {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ (1 + (Fintype.card X : ℝ) * α) * f S := by sorry

end NonmonotoneSubmod.LocalSearch
