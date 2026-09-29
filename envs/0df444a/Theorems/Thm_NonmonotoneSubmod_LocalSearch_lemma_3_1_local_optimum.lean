-- Prove2me | Theorems.Thm_NonmonotoneSubmod_LocalSearch_lemma_3_1_local_optimum
-- name    : NonmonotoneSubmod.LocalSearch.lemma_3_1_local_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:01:00.723882+00:00
-- url     : https://prove2.me/theorems/c920a1bb-cd80-40c2-9de9-cd0df43048c1
-- title:
--   Lemma 3.1 — a local optimum dominates its subsets and supersets
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be a submodular function on a finite ground set $X$, and let $S \subseteq X$ be a local optimum of $f$: adding an element outside $S$ or removing an element of $S$ never increases $f$. Then for every $T \subseteq X$ with $T \subseteq S$ or $T \supseteq S$,
--
--   $$f(T) \le f(S).$$
--
--   This property, first observed by Cherenin and by Goldengorin et al., is the basis for comparing local optima with the global optimum in local-search analyses of submodular maximization.
--
--   **Formalization Note** No sign condition is placed on $f$; the lemma is stated for every real-valued submodular $f$, as printed.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1140, Lemma 3.1

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

/-- Lemma 3.1 (Feige–Mirrokni–Vondrák 2011, p. 1140): for a submodular `f`, if `S` is a local
optimum of `f` and `T ⊆ S` or `T ⊇ S`, then `f(T) ≤ f(S)`. -/
theorem lemma_3_1_local_optimum {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (hS : IsLocalOptimum f S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ f S := by sorry

end NonmonotoneSubmod.LocalSearch
