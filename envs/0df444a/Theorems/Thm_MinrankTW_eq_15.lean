-- Prove2me | Theorems.Thm_MinrankTW_eq_15
-- name    : MinrankTW.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:10.682111+00:00
-- url     : https://prove2.me/theorems/6882d229-96df-4af1-9e15-795c5610936b
-- title:
--   Eq. (15) — $\left[{b\atop j}\right]_q=\Theta_q(q^{j(b-j)})$ and $N_q(b)=\Theta_q(q^{\lfloor b^2/4\rfloor})$
-- statement:
--   Over $\mathbb F_q$, let $\left[{b\atop j}\right]_q$ count the $j$-dimensional subspaces of $\mathbb F_q^b$ and $N_q(b)$ all subspaces. Then:
--
--   1. counting ordered bases, for $j\le b$
--   $$
--   \left[{b\atop j}\right]_q\prod_{i=0}^{j-1}(q^j-q^i)=\prod_{i=0}^{j-1}(q^b-q^i);
--   $$
--   2. $N_q(b)=\sum_{j=0}^b\left[{b\atop j}\right]_q$;
--   3. there are constants $0<c\le C$ depending only on $q$ with $c\,q^{j(b-j)}\le\left[{b\atop j}\right]_q\le C\,q^{j(b-j)}$ for all $b$ and $j\le b$;
--   4. there are constants $0<c\le C$ depending only on $q$ with $c\,q^{\lfloor b^2/4\rfloor}\le N_q(b)\le C\,q^{\lfloor b^2/4\rfloor}$ for all $b$.
--
--   A bag of size $b$ therefore has $\Theta_q(q^{\lfloor b^2/4\rfloor})$ states, which is the source of the exponent $\lfloor (w+1)^2/4\rfloor$ of Theorem 2.
--
--   Differences from the source:
--   - encoding: the quotient formula ∏(q^b − q^i)/(q^j − q^i) → the same identity multiplied out; reason: the denominators are positive; same content
--   - encoding: Θ_q(·) → explicit constants 0 < c, 0 < C chosen after F and before b, j, both directions; reason: definition of Θ with constants depending only on q
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.3, p.12, Eq. (15)

import Mathlib
import Definitions.Def_MinrankTW_Nq
import Definitions.Def_MinrankTW_gaussCount

namespace MinrankTW

/-- **Eq. (15)** (Number of states), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §3.3, p.12. Over `F_q`:
1. counting ordered bases, `[b j]_q = ∏_{i<j} (q^b − q^i)/(q^j − q^i)` (stated without division:
   `[b j]_q · ∏_{i<j}(q^j − q^i) = ∏_{i<j}(q^b − q^i)`, for `j ≤ b`);
2. `N_q(b) = ∑_{j=0}^{b} [b j]_q`;
3. `[b j]_q = Θ_q(q^{j(b−j)})`, with constants depending only on `q`, uniformly in `b` and
   `j ≤ b`;
4. `N_q(b) = Θ_q(q^{⌊b²/4⌋})`, with constants depending only on `q`.

**Formalization Note** `q = |F|`; both directions of each `Θ` are stated with real constants
`0 < c`, `0 < C` chosen after `F` and before `b, j`. `⌊b²/4⌋` is natural-number division. -/
theorem eq_15 (F : Type) [Field F] [Fintype F] :
    (∀ b j : ℕ, j ≤ b →
      gaussCount F b j * ∏ i ∈ Finset.range j, (Fintype.card F ^ j - Fintype.card F ^ i) =
        ∏ i ∈ Finset.range j, (Fintype.card F ^ b - Fintype.card F ^ i)) ∧
    (∀ b : ℕ, Nq F b = ∑ j ∈ Finset.range (b + 1), gaussCount F b j) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ b j : ℕ, j ≤ b →
      c * (Fintype.card F : ℝ) ^ (j * (b - j)) ≤ gaussCount F b j ∧
        (gaussCount F b j : ℝ) ≤ C * (Fintype.card F : ℝ) ^ (j * (b - j))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ b : ℕ,
      c * (Fintype.card F : ℝ) ^ (b ^ 2 / 4) ≤ Nq F b ∧
        (Nq F b : ℝ) ≤ C * (Fintype.card F : ℝ) ^ (b ^ 2 / 4)) := by sorry

end MinrankTW
