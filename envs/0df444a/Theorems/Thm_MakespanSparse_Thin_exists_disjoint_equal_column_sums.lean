-- Prove2me | Theorems.Thm_MakespanSparse_Thin_exists_disjoint_equal_column_sums
-- name    : MakespanSparse.Thin.exists_disjoint_equal_column_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:21.718992+00:00
-- url     : https://prove2.me/theorems/963ff0c4-ae40-4055-82a1-29480ac71509
-- title:
--   Lemma 2, p. 4 (Eisenbrand–Shmonin) — a large support contains disjoint nonempty A, B with Mx^A = Mx^B
-- statement:
--   Let $\pi \in \mathbb{Z}^d_{>0}$, $T \in \mathbb{Z}_{>0}$, and let $Q$ be the set of configurations $c \in \mathbb{Z}^d_{\ge 0}$ with $\pi \cdot c \le T$ (logarithms are to base 2). Let $M$ be the $(d+1) \times |Q|$ matrix of the equality system of [conf-IP], whose column for $c$ is $(c, 1)$, and for $A \subseteq Q$ let $x^A$ be the indicator vector of $A$, so that $M x^A = \bigl(\sum_{c \in A} c,\ |A|\bigr)$.
--
--   Let $x \in \mathbb{Z}^Q_{\ge 0}$ with
--
--   $$|\operatorname{supp}(x)| > 2(d+1)\log(4(d+1)T).$$
--
--   Then there exist two disjoint sets $A, B$ with $\emptyset \ne A, B \subseteq \operatorname{supp}(x)$ such that $M x^A = M x^B$, that is, $\sum_{c\in A} c = \sum_{c \in B} c$ and $|A| = |B|$.
--
--   This is the exchange step behind the Eisenbrand–Shmonin support bound: moving weight from $A$ to $B$ keeps a solution feasible while one variable drops to zero.
--
--   **Formalization Note** $x$ is any finitely supported nonnegative integer vector vanishing off $Q$; no feasibility is assumed. The identity $M x^A = M x^B$ is stated row by row: the first $d$ rows as the equality of the two vector sums, the last row as $|A| = |B|$.
-- source:
--   arXiv:1604.07153v1, Lemma 2, p. 4

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP

namespace MakespanSparse.Thin

/-- Lemma 2 (Eisenbrand and Shmonin), arXiv:1604.07153v1, p. 4. `Mx^A = Mx^B` is written row by
row: the first `d` rows give `∑_{c ∈ A} c = ∑_{c ∈ B} c`, the last row gives `|A| = |B|`. -/
theorem exists_disjoint_equal_column_sums (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k)
    (T : ℕ) (hT : 0 < T)
    (x : (Fin d → ℕ) →₀ ℕ) (hx : ∀ c ∈ x.support, IsConfig π T c)
    (hs : (x.support.card : ℝ) > 2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T)) :
    ∃ A B : Finset (Fin d → ℕ), A ⊆ x.support ∧ B ⊆ x.support ∧ Disjoint A B ∧
      A.Nonempty ∧ B.Nonempty ∧ ∑ c ∈ A, c = ∑ c ∈ B, c ∧ A.card = B.card := by sorry

end MakespanSparse.Thin
