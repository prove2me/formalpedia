-- Prove2me | Theorems.Thm_HighDimProb_RandomVectors_grothendieck_inequality
-- name    : HighDimProb.RandomVectors.grothendieck_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-18T06:44:36.745533+00:00
-- url     : https://prove2.me/theorems/b14acc86-2194-4cd3-a200-5e1829f89715
-- title:
--   Theorem 3.5.1 — Grothendieck's inequality
-- statement:
--   This is **Grothendieck's inequality** (Theorem 3.5.1), the goal theorem of this mission: a
--   purely deterministic, non-probabilistic statement about bilinear forms on $\{-1,1\}$-valued
--   vectors and their behavior once those signs are replaced by unit vectors in an arbitrary
--   Hilbert space, proved here (Section 3.5) by a probabilistic argument using high-dimensional
--   Gaussian vectors.
--
--   There is an absolute constant $K$, $0 < K \le 288$, such that the following holds. Let
--   $m, n \in \mathbb N$ and let $A = (a_{ij})$ be a real $m \times n$ matrix such that, for
--   every choice of numbers $x_1, \dots, x_m, y_1, \dots, y_n \in \{-1, 1\}$,
--
--   $$
--   \Bigl| \sum_{i,j} a_{ij}\, x_i y_j \Bigr| \;\le\; 1 .
--   $$
--
--   Then, for every (real) Hilbert space $H$ and every choice of vectors $u_1, \dots, u_m, v_1,
--   \dots, v_n \in H$ with $\|u_i\| = \|v_j\| = 1$,
--
--   $$
--   \Bigl| \sum_{i,j} a_{ij}\, \langle u_i, v_j \rangle \Bigr| \;\le\; K .
--   $$
--
--   The remarkable content is that $K$ does not depend on the matrix $A$, on the dimensions $m,
--   n$, or on the Hilbert space $H$ — a bound that holds for scalars ($H = \mathbb R$) survives,
--   with the same absolute constant, passage to an arbitrary (even infinite-dimensional) inner
--   product space.
--
--   **Formalization Note** This chunk formalizes the chapter's own first-pass bound $K \le 288$
--   (Section 3.5, by Gaussian truncation), not the sharper $K \le 1.783$ of Section 3.7 (the
--   kernel-trick argument), which lies outside this chunk's chapter range; $K \le 288$ is a
--   complete, book-stated theorem in its own right, not a weakening of Theorem 3.5.1 — see
--   `STATUS.md` for the reasoning. $K$ is existentially quantified ahead of every other object
--   (the matrix, its dimensions, and the Hilbert space $H$), so a single $K$ must work
--   uniformly, matching the book's claim that $K$ is an absolute constant.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 3.5.1, p. 61 (PDF p. 69); K ≤ 288 bound proved p. 61-63 (PDF p. 69-71)

import Mathlib

namespace HighDimProb.RandomVectors

/-- **Theorem 3.5.1** (Grothendieck's inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 61.

Consider an `m × n` matrix `(aᵢⱼ)` of real numbers. Assume that for any numbers `xᵢ, yⱼ ∈
{−1, 1}`, `|∑ᵢⱼ aᵢⱼ xᵢ yⱼ| ≤ 1`. Then, for any Hilbert space `H` and any vectors `uᵢ, vⱼ ∈ H`
with `‖uᵢ‖ = ‖vⱼ‖ = 1`, `|∑ᵢⱼ aᵢⱼ ⟨uᵢ, vⱼ⟩| ≤ K`, where `K ≤ 288` is an absolute constant.

This is the chapter's first-pass bound `K ≤ 288` (Section 3.5), proved by Gaussian truncation;
Section 3.7's sharper `K ≤ 1.783` argument (the kernel trick) is out of scope for this chunk. -/
theorem grothendieck_inequality :
    ∃ K : ℝ, 0 < K ∧ K ≤ 288 ∧
      ∀ {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ),
        (∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
          (∀ j, y j = 1 ∨ y j = -1) → |∑ i, ∑ j, a i j * x i * y j| ≤ 1) →
        ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
          (u : Fin m → H) (v : Fin n → H),
          (∀ i, ‖u i‖ = 1) → (∀ j, ‖v j‖ = 1) →
          |∑ i, ∑ j, a i j * inner ℝ (u i) (v j)| ≤ K := by sorry

end HighDimProb.RandomVectors
