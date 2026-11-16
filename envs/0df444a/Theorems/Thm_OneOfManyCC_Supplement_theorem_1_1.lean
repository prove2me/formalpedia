-- Prove2me | Theorems.Thm_OneOfManyCC_Supplement_theorem_1_1
-- name    : OneOfManyCC.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:21:35.852246+00:00
-- url     : https://prove2.me/theorems/55de30ac-7f01-4e10-a9b4-43d4eae0300c
-- title:
--   Theorem 1.1 — $\mathrm{CC}(F)-O(\log k+\log n)\le\mathrm{CC}(\mathrm{OneOut}^{\neq}_k(F))\le\mathrm{CC}(F)$ for Boolean $F$
-- statement:
--   Let $A$ and $B$ be finite sets with $|A|,|B|\le 2^n$, where $n\ge 1$, and let $F:A\times B\to\{0,1\}$ be a total Boolean function, identified with the relation $\{(x,y,F(x,y))\}$. In the **1-out-of-$k$ problem** $\mathrm{OneOut}^{\neq}_k(F)$, Alice receives pairwise distinct $x_1,\dots,x_k\in A$, Bob receives pairwise distinct $y_1,\dots,y_k\in B$, and they must output an index $i$ together with the value $F(x_i,y_i)$. Write $\mathrm{CC}$ for deterministic communication complexity.
--
--   There is an absolute constant $C>0$ such that for all such $A$, $B$, $F$, $n$ and every $1\le k\le\min\{|A|,|B|\}$,
--   $$\mathrm{CC}(F)-C(\log_2 k+\log_2 n)\;\le\;\mathrm{CC}(\mathrm{OneOut}^{\neq}_k(F))\;\le\;\mathrm{CC}(F).$$
--
--   So letting the players choose which of $k$ distinct instances to solve saves at most $O(\log k+\log n)$ bits, and never makes the problem harder. This is the Boolean-function form of the mission's goal, Theorem 1.2.
--
--   **Formalization Note** $F$ is `A → B → Bool` and its relation is `fun x y b => F x y = b`. $\mathrm{CC}$, $\mathrm{OneOut}$ are the mission's published definitions (tuples are `Fin k ↪ A`, indices 0-based).
--
--   Differences from the source:
--   - encoding: F : A × B → {0,1} identified with the total relation {(x, y, F(x, y))} → F : A → B → Bool with relation fun x y b => F x y = b; reason: the identification of p.8; Bool is {0,1}
--   - encoding: O(log k + log n) → one absolute constant C > 0 chosen before every type and parameter, with base-2 logarithms (Real.logb 2); reason: the paper's O(·) hides an absolute constant; logarithms are base 2 (§3)
--   - encoding: finite sets A, B; Inj_k(A); index i ∈ [k] → types with Fintype; the published OneOut on Fin k ↪ A, 0-based Fin k; reason: the same tuples of pairwise distinct elements and the same indices
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.1, p.1 (PDF p.2); restated and proved p.9 (PDF p.10)

import Mathlib
import Definitions.Def_OneOfManyCC_CC
import Definitions.Def_OneOfManyCC_OneOut

namespace OneOfManyCC.Supplement

open OneOfManyCC

/-- **Theorem 1.1.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.1, p.1 (restated p.9):
"For every total F : A × B → {0, 1} with |A|, |B| ≤ 2ⁿ, n ≥ 1, and every 1 ≤ k ≤ min{|A|, |B|},
CC(F) − O(log k + log n) ≤ CC(OneOut≠ₖ(F)) ≤ CC(F)."

**Formalization Note.** A function `F : A → B → Bool` is identified with the total relation
`{(x, y, F x y)}` (p.8), here `fun x y b => F x y = b`. The `O(·)` is one absolute constant `C`,
chosen before all types and parameters. Logarithms are base 2. Both inequalities are stated. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (F : A → B → Bool) (n k : ℕ),
      Fintype.card A ≤ 2 ^ n → Fintype.card B ≤ 2 ^ n → 1 ≤ n →
      1 ≤ k → k ≤ min (Fintype.card A) (Fintype.card B) →
        (CC (fun x y b => F x y = b) : ℝ) - C * (Real.logb 2 k + Real.logb 2 n)
            ≤ (CC (OneOut k (fun x y b => F x y = b)) : ℝ) ∧
          CC (OneOut k (fun x y b => F x y = b)) ≤ CC (fun x y b => F x y = b) := by sorry

end OneOfManyCC.Supplement
