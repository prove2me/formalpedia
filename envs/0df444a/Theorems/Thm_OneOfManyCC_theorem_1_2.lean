-- Prove2me | Theorems.Thm_OneOfManyCC_theorem_1_2
-- name    : OneOfManyCC.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:41.543601+00:00
-- url     : https://prove2.me/theorems/220463f0-0ab5-4e94-a4ed-19bb87a41d19
-- title:
--   Theorem 1.2 — $\mathrm{CC}(R)\le\max\{\mathrm{CC}(\mathrm{OneOut}^{\neq}_k(R)),\lceil\log_2|O|\rceil\}+O(\log k+\log n)$
-- statement:
--   Let $R\subseteq A\times B\times O$ be a total relation on finite nonempty sets, with $|A|,|B|\le 2^n$. For every $1\le k\le\min\{|A|,|B|\}$,
--
--   $$\mathrm{CC}(R)\le\max\bigl\{\mathrm{CC}(\mathrm{OneOut}^{\neq}_k(R)),\ \lceil\log_2|O|\rceil\bigr\}+O(\log k+\log n).$$
--
--   The constant in $O(\cdot)$ is absolute. So when Alice holds $k$ distinct inputs and Bob holds $k$ distinct inputs, the freedom to choose which instance to solve saves only $O(\log k+\log n)$ bits, unless the bound is dominated by $\lceil\log_2|O|\rceil$. This is the paper's main result; the Boolean case gives Theorem 1.1, and $O=[n]$ with Karchmer–Wigderson games gives its formula-depth bound.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → one constant $C>0$ quantified before all types and parameters; reason: the paper's $O(\cdot)$ depends on nothing
--   - encoding: finite nonempty sets → no `Nonempty` binders; reason: $1\le k\le\min\{|A|,|B|\}$ makes $A,B$ nonempty, and totality then makes $O$ nonempty
--   - encoding: $n$ with $|A|,|B|\le 2^n$ → any natural number $n$, with `Real.logb 2 0 = 0`; reason: the theorem states no $n\ge1$; at $n=0$ we have $|A|=|B|=k=1$ and $\mathrm{CC}(R)\le\mathrm{CC}(\mathrm{OneOut}^{\neq}_1(R))$ holds with no additive term
--   - encoding: $\log$ inside $O(\cdot)$ and $\lceil\log_2\cdot\rceil$ → `Real.logb 2` and `Nat.clog 2`; reason: the paper's logarithms are base 2; `Nat.clog 2 m` is $\lceil\log_2 m\rceil$ for $m\ge1$ and `Real.logb 2 0 = 0`
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
--   - encoding: $\mathrm{Inj}_k(A)$ → the embeddings `Fin k ↪ A`; reason: injective maps from $k$ positions are exactly the $k$-tuples of pairwise distinct elements
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.2, p.1

import Mathlib
import Definitions.Def_OneOfManyCC_CC
import Definitions.Def_OneOfManyCC_OneOut

namespace OneOfManyCC

/-- **Theorem 1.2.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.2, p.1:
"Let R ⊆ A × B × O be a total relation on finite nonempty sets, with |A|, |B| ≤ 2ⁿ. For every
1 ≤ k ≤ min{|A|, |B|}, CC(R) ≤ max{CC(OneOut≠ₖ(R)), ⌈log₂|O|⌉} + O(log k + log n)."

**Formalization Note.** The `O(·)` is one absolute constant `C`, chosen before all types and
parameters. Nonemptiness of `A`, `B`, `O` follows from `1 ≤ k ≤ min{|A|, |B|}` and totality. `n` is any
natural number; `Real.logb 2 0 = 0`, and at `n = 0` the case `|A| = |B| = k = 1` is true with no
additive term. Logarithms are base `2`. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B O : Type) [Fintype A] [Fintype B] [Fintype O]
      (R : A → B → O → Prop), IsTotal R →
      ∀ (n k : ℕ), Fintype.card A ≤ 2 ^ n → Fintype.card B ≤ 2 ^ n →
        1 ≤ k → k ≤ min (Fintype.card A) (Fintype.card B) →
        (CC R : ℝ) ≤ max (CC (OneOut k R) : ℝ) (Nat.clog 2 (Fintype.card O) : ℝ)
          + C * (Real.logb 2 k + Real.logb 2 n) := by sorry

end OneOfManyCC
