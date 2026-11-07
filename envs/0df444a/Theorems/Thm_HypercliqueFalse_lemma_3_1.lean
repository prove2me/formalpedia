-- Prove2me | Theorems.Thm_HypercliqueFalse_lemma_3_1
-- name    : HypercliqueFalse.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:29:58.089057+00:00
-- url     : https://prove2.me/theorems/e92a4e96-07fd-48de-9580-d0345dfca215
-- title:
--   Lemma 3.1 (Swap Identity)
-- statement:
--   Let $q \ge 2$ and let $U_{ij} \in \mathbb Z^{a\times b}$ and $V_{ij} \in \mathbb Z^{b \times a}$ for all $i, j \in [q]$. Then
--   $$
--   \sum_{i,j\in[q]} \operatorname{tr}(U_{ij}V_{ij}) = \sum_{i,j\in[q]} \operatorname{tr}(U_{ij}V_{ji}) + \sum_{1\le i<j\le q}\operatorname{tr}\big((U_{ij}-U_{ji})(V_{ij}-V_{ji})\big).
--   $$
--
--   This identity regroups the $q^2$ terms of a split polynomial into $q$ "main" terms and $\binom q2$ "correction" terms; it is the algebraic core of the recursive step (Lemma 4.1).
--
--   Differences from the source:
--   - encoding: indices i, j ∈ [q] = {1, …, q} → Fin q (0-based); the sum over 1 ≤ i < j ≤ q is ∑ i, ∑ j ∈ Finset.Ioi i; reason: Lean convention; same identity
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 3.1, p.6

import Mathlib

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Lemma 3.1 (Swap Identity).** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 3.1, p.6: "Let q ≥ 2, and
let U_{ij} ∈ Z^{a×b}, V_{ij} ∈ Z^{b×a} for all i, j ∈ [q]. Then:
Σ_{i,j∈[q]} tr(U_{ij}V_{ij}) = Σ_{i,j∈[q]} tr(U_{ij}V_{ji}) + Σ_{1≤i<j≤q} tr((U_{ij} − U_{ji})(V_{ij} − V_{ji}))."

**Formalization Note.** Indices `[q]` are `Fin q` (0-based); the last sum is over `j ∈ Ioi i`, i.e.
`i < j`. -/
theorem lemma_3_1 (q a b : ℕ) (hq : 2 ≤ q) (U : Fin q → Fin q → Matrix (Fin a) (Fin b) ℤ)
    (V : Fin q → Fin q → Matrix (Fin b) (Fin a) ℤ) :
    ∑ i, ∑ j, (U i j * V i j).trace =
      ∑ i, ∑ j, (U i j * V j i).trace +
        ∑ i, ∑ j ∈ Finset.Ioi i, ((U i j - U j i) * (V i j - V j i)).trace := by sorry

end HypercliqueFalse
