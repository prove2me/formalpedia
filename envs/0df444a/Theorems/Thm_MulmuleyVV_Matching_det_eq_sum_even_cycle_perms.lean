-- Prove2me | Theorems.Thm_MulmuleyVV_Matching_det_eq_sum_even_cycle_perms
-- name    : MulmuleyVV.Matching.det_eq_sum_even_cycle_perms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:36:28.999453+00:00
-- url     : https://prove2.me/theorems/14f564b0-273d-45a9-a9e5-b99cb2095656
-- title:
--   Proof of Lemma 2 — permutations with an odd cycle cancel in the determinant of a skew-symmetric matrix
-- statement:
--   Let $B = (b_{ij})$ be an $n \times n$ skew-symmetric integer matrix, $B^{\mathsf T} = -B$. For a permutation $\sigma$ of $\{1, \dots, n\}$ put $\operatorname{value}(\sigma) = \prod_{i=1}^n b_{i\sigma(i)}$, so that $|B| = \sum_\sigma \operatorname{sign}(\sigma)\operatorname{value}(\sigma)$. Then the permutations with an odd cycle contribute nothing:
--
--   $$
--   |B| \;=\; \sum_{\substack{\sigma \,:\, \text{every cycle of } \sigma \\ \text{has even length}}} \operatorname{sign}(\sigma)\,\operatorname{value}(\sigma),
--   $$
--
--   where fixed points count as cycles of length $1$ and are therefore excluded.
--
--   In the paper this is the step of Lemma 2's proof where a permutation with an odd cycle is paired with the permutation that traverses that cycle in the opposite direction; the same cancellation is used again in Lemma 3. It applies in particular to the matrix $B$ obtained from the Tutte matrix.
--
--   **Formalization Note** Stated for an arbitrary skew-symmetric matrix over $\mathbb{Z}$ (which has zero diagonal); the paper uses it for its matrix $B$. "Every cycle has even length" is `(∀ i, σ i ≠ i) ∧ ∀ k ∈ σ.cycleType, Even k`, since Mathlib's `cycleType` omits fixed points.
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), p. 108, proof of Lemma 2 (second and third paragraphs; unnumbered)

import Mathlib

namespace MulmuleyVV.Matching

theorem det_eq_sum_even_cycle_perms {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.transpose = -B) :
    B.det = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (∀ i, σ i ≠ i) ∧ ∀ k ∈ σ.cycleType, Even k),
      (Equiv.Perm.sign σ : ℤ) * ∏ i, B i (σ i) := by sorry

end MulmuleyVV.Matching
