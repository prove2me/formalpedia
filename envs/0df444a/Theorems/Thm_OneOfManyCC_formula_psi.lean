-- Prove2me | Theorems.Thm_OneOfManyCC_formula_psi
-- name    : OneOfManyCC.formula_psi
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:34.211277+00:00
-- url     : https://prove2.me/theorems/dfd7f559-3480-4a24-a0d6-18fa2f26bee0
-- title:
--   §5, proof of Theorem 1.2 — a formula $\Psi$ of depth $O(\log k+\log n)$ over solvable rectangles, zero on $A$, one on $B$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $R$ be a total relation on finite sets with $|A|,|B|\le 2^n$, and let $1\le k\le\min\{|A|,|B|\}$. There is a formula $\Psi$ with AND and OR gates, whose leaves are solvable rectangles $A'\times B'$ valued by the functions $\mathbf 1[x\notin A']$ on $A$ and $\mathbf 1[y\in B']$ on $B$, with depth at most
--
--   $$C\,(\log_2k+\log_2n),$$
--
--   that is zero at every $x\in A$ and one at every $y\in B$. It is the plan of the final protocol: the players walk down $\Psi$ to a rectangle containing their inputs.
--
--   Differences from the source:
--   - encoding: leaves from $\mathcal F$, the functions of solvable rectangles → leaves typed as the solvable rectangles, valued by `rectFn`; reason: a rectangle is determined by its function
--   - encoding: $O(\cdot)$ → one constant $C>0$ quantified before all parameters; reason: the paper's $O(\cdot)$ is absolute; at $k=1$, $n\le1$ the bound is $0$, and the statement still holds since $(A,B)$ is then solvable
--   - encoding: $n$ with $|A|,|B|\le 2^n$ → any natural number $n$, with `Real.logb 2 0 = 0`; reason: Theorem 1.2 states no $n\ge1$; at $n=0$ we have $|A|=|B|=k=1$ and $\Psi$ is one leaf
--   - encoding: $\log$ inside $O(\cdot)$ and $\lceil\log_2\cdot\rceil$ → `Real.logb 2` and `Nat.clog 2`; reason: the paper's logarithms are base 2; `Nat.clog 2 m` is $\lceil\log_2 m\rceil$ for $m\ge1$ and `Real.logb 2 0 = 0`
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
--   - encoding: $\mathrm{Inj}_k(A)$ → the embeddings `Fin k ↪ A`; reason: injective maps from $k$ positions are exactly the $k$-tuples of pairwise distinct elements
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Theorem 1.2, p.12

import Mathlib
import Definitions.Def_OneOfManyCC_Formula
import Definitions.Def_OneOfManyCC_rectFn

namespace OneOfManyCC

/-- **The formula Ψ over solvable rectangles.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Theorem 1.2, p.12:
"Since |A ⊔ B| ≤ 2ⁿ⁺¹, Lemma 3.7 with Z = A ⊔ B and ε = k⁻²/4 gives a formula Ψ of depth
O(log k + log n) with leaves from F that is zero at every x ∈ A and one at every y ∈ B."

**Formalization Note.** The constant is absolute. Leaves are typed as the solvable rectangles and
valued by `rectFn`. At `k = 1`, `n ≤ 1` the depth bound is `0`; the statement holds there because
`(A, B)` is itself solvable, so `Ψ` is that leaf. `Real.logb 2 0 = 0` at `n = 0`. -/
theorem formula_psi :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B O : Type) [Fintype A] [Fintype B] [Fintype O]
      (R : A → B → O → Prop), IsTotal R →
      ∀ (n k : ℕ), Fintype.card A ≤ 2 ^ n → Fintype.card B ≤ 2 ^ n →
        1 ≤ k → k ≤ min (Fintype.card A) (Fintype.card B) →
        ∃ Ψ : Formula (SolvableRect k R),
          (Ψ.depth : ℝ) ≤ C * (Real.logb 2 k + Real.logb 2 n) ∧
          (∀ x : A, Ψ.eval rectFn (Sum.inl x) = false) ∧
          (∀ y : B, Ψ.eval rectFn (Sum.inr y) = true) := by sorry

end OneOfManyCC
