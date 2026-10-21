-- Prove2me | Theorems.Thm_IwataFF_SFM_theorem_4_2
-- name    : IwataFF.SFM.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:22.287974+00:00
-- url     : https://prove2.me/theorems/88eba2a3-8338-46ca-abb5-131f3a8d8b5d
-- title:
--   Theorem 4.2 — the algorithm of Figure 3 minimizes every real submodular function in $O(n^7 \log n)$ steps
-- statement:
--   There is an absolute constant $C \in \mathbb{N}$ such that for every $n \ge 1$ and every real submodular function $f$ on the subsets of $V = \{0, \dots, n-1\}$ with $f(\emptyset) = 0$, the algorithm of Figure 3 (with Fix and its scaling phases as defined in `IwataFF.SFM.Phase` and `IwataFF.SFM.Main`) satisfies:
--
--   1. **Progress.** Every state reachable from the initial state that is not final has a successor.
--   2. **Running time.** Every run $s_0 \to s_1 \to \dots \to s_k$ from the initial state has
--   $$k \le C \cdot n^7 \cdot (\lfloor \log_2 n \rfloor + 1).$$
--   3. **Correctness.** Every final state reachable from the initial state outputs a set $X$ with $f(X) \le f(Y)$ for every $Y \subseteq V$.
--
--   Since $C$ does not depend on $f$, the bound is strongly polynomial: it depends on the size of the underlying set only, not on the function values.
--
--   **Formalization Note** A step is a phase start, a single push, a single augmentation with its reduction, a call of Fix, a return from Fix (with its contraction, arc addition or deletion), or the final step; the arithmetic cost of a step is not modeled, so "time" is the number of these operations. $O(n^7 \log n)$ became $\exists C$ quantified before $n$ and $f$, with $\lfloor\log_2 n\rfloor + 1$ so that the bound does not vanish at $n = 1$. Progress rules out a model in which the algorithm gets stuck and the other two conjuncts hold vacuously. Fix is the scaling algorithm of §3 run until $\delta < \kappa/n^3$, not an oracle.
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 13, Theorem 4.2 (Figure 3, p. 14)

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
import Definitions.Def_IwataFF_SFM_Main

namespace IwataFF.SFM

/-- Theorem 4.2 (arXiv:math/0004089v1, p. 13): the algorithm in Figure 3 computes a minimizer of
a submodular function in `O(n⁷ log n)` steps (strongly polynomial): every reachable non-final
state has a successor, every run has at most `C · n⁷ · (⌊log₂ n⌋ + 1)` steps with `C` absolute,
and every final state's output minimizes `f`. -/
theorem theorem_4_2 :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ f : Finset (Fin n) → ℝ,
      SubmodularOn Finset.univ f → f ∅ = 0 →
      (∀ s : MainState n, Relation.ReflTransGen Step (initMain f) s → ¬ IsFinal s →
          ∃ s' : MainState n, Step s s') ∧
      (∀ (s : ℕ → MainState n) (k : ℕ), IsRun f s k → k ≤ C * n ^ 7 * (Nat.log 2 n + 1)) ∧
      (∀ (s : MainState n) (X : Finset (Fin n)), Relation.ReflTransGen Step (initMain f) s →
          s.mode = Mode.done X → ∀ Y : Finset (Fin n), f X ≤ f Y) := by sorry

end IwataFF.SFM
