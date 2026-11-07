-- Prove2me | Theorems.Thm_MatSemiBurnside_eq_9
-- name    : MatSemiBurnside.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:41.530444+00:00
-- url     : https://prove2.me/theorems/c94a024a-50da-455c-88b0-b48e3addc0a9
-- title:
--   Decomposition (9): $a_1\cdots a_k=(y_1c_1)\cdots(y_\ell c_\ell)y_{\ell+1}$
-- statement:
--   Let $d$ be a positive integer, $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ finite and nonempty and $\sim$ a congruence on $\langle X\rangle$. Let $a_1\cdots a_k$, with $a_i\in X$ and $k\ge1$, represent a class whose minimum rank is $r$. Then the word $a_1\cdots a_k$ decomposes as
--   $$a_1\cdots a_k=(y_1c_1)\cdots(y_\ell c_\ell)\,y_{\ell+1},\qquad \ell\ge1,$$
--   where
--
--   1. each $c_i\in X$;
--   2. each class $[y_ic_i]_\sim$ has minimum rank $r$;
--   3. every $y_i$, including the final suffix $y_{\ell+1}$, is either empty or represents a class of minimum rank greater than $r$.
--
--   This decomposition lets the proof replace each factor $y_ic_i$ by a fixed rank-$r$ representative and apply Claim 3.2.
--
--   **Formalization Note** The decomposition is an identity of words (lists over $X$); "$[w]_\sim$ has minimum rank $s$" for a nonempty word $w$ means that the class represented by $w$ has minimum rank $s$.
--
--   Differences from the source:
--   - encoding: the decomposition a_1 ⋯ a_k = (y_1c_1) ⋯ (y_ℓc_ℓ)y_{ℓ+1} → lists `ys`, `cs` of equal length ℓ ≥ 1 and a suffix `z` with `l = flatten (zipWith (y ++ [c])) ++ z`; reason: the same factorisation of the word
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, eq. (9), p.31

import Mathlib
import Definitions.Def_MatSemiBurnside_IsProdRepr
import Definitions.Def_MatSemiBurnside_minRank
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Decomposition (9).** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, eq. (9), p.31: "Let a1 · · · ak, with
ai ∈ X, represent any class whose minimum rank is r. It admits a decomposition
a1 · · · ak = (y1c1) · · · (yℓcℓ)yℓ+1, (9) where ci ∈ X, each [yici]∼ has minimum rank r, and every
yi, including the final suffix, is either empty or belongs to a class of minimum rank greater than
r." and "Since the full class has minimum rank r, at least one factor yici is selected."

**Formalization Note.** The word a₁ ⋯ a_k is a nonempty list `l` over X; the decomposition is a word
identity: `ys = [y₁, …, y_ℓ]`, `cs = [c₁, …, c_ℓ]` (ℓ ≥ 1) and the suffix `z = y_{ℓ+1}` with
`l = y₁ ++ [c₁] ++ ⋯ ++ y_ℓ ++ [c_ℓ] ++ z`. "[w]∼ has minimum rank s" for a nonempty word w over X
is: the class represented by w has `minRank` s (`IsProdRepr`). -/
theorem eq_9 {d : ℕ} (hd : 0 < d) (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (hX : X.Nonempty)
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (l : List (Matrix (Fin d) (Fin d) ℚ)) (r : ℕ)
    (hl : ∃ q, IsProdRepr X c l q ∧ minRank c q = r) :
    ∃ (ys : List (List (Matrix (Fin d) (Fin d) ℚ))) (cs : List (Matrix (Fin d) (Fin d) ℚ)) (z : List (Matrix (Fin d) (Fin d) ℚ)),
      ys.length = cs.length ∧ 1 ≤ cs.length ∧
      l = (List.zipWith (fun y x => y ++ [x]) ys cs).flatten ++ z ∧
      (∀ x ∈ cs, x ∈ X) ∧
      (∀ p ∈ ys.zip cs, ∃ q, IsProdRepr X c (p.1 ++ [p.2]) q ∧ minRank c q = r) ∧
      (∀ y ∈ z :: ys, y = [] ∨ ∃ q, IsProdRepr X c y q ∧ r < minRank c q) := by sorry

end MatSemiBurnside
