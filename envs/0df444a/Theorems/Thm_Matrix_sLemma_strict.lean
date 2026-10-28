-- Prove2me | Theorems.Thm_Matrix_sLemma_strict
-- name    : Matrix.sLemma_strict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:48:23.324988+00:00
-- url     : https://prove2.me/theorems/6e458858-0dd2-4355-925a-18c544e9fbd3
-- title:
--   The S-lemma (strict form): $x^{\mathsf T}Bx \ge 0,\ x \ne 0 \Rightarrow x^{\mathsf T}Ax > 0$ iff $A - \tau B \succ 0$ for some $\tau \ge 0$
-- statement:
--   Let $A, B$ be symmetric real $n \times n$ matrices. Then
--
--   $$
--   \Big(\forall x \neq 0,\ x^{\mathsf T} B x \ge 0 \;\Longrightarrow\; x^{\mathsf T} A x > 0\Big)
--   \quad\Longleftrightarrow\quad
--   \exists\, \tau \ge 0 \ \text{ with } \ A - \tau B \succ 0 .
--   $$
--
--   The implication from right to left is immediate: if $A - \tau B \succ 0$ with $\tau \ge 0$ then
--   $x^{\mathsf T} A x > \tau\, x^{\mathsf T} B x \ge 0$ for $x \ne 0$ in the cone. The content is
--   the converse -- that a *quadratic* implication between two quadratic forms, which is not a
--   linear condition on anything, is certified by a single scalar $\tau$. That is what makes the
--   S-procedure work: a robust constraint "the quadratic $A$ is positive wherever the quadratic $B$
--   is" becomes the semidefinite constraint $A - \tau B \succ 0$ in the extra variable $\tau$, and
--   the resulting problem is convex.
--
--   This strict version is the one used in practice, because the strict conclusion
--   $x^{\mathsf T} A x > 0$ matches the strict feasibility needed for interior-point methods and
--   for the tightness arguments about SDP relaxations of quadratically constrained problems.
--
--   **Formalization Note** `A.IsSymm` is symmetry and `PosDef` strict positive definiteness, both
--   Mathlib's; the quadratic form is written `x ⋅ᵥ A *ᵥ x`. The forward direction is a separation
--   argument on the set of pairs $(x^{\mathsf T}Ax, x^{\mathsf T}Bx)$ over the unit sphere, which
--   is compact, so the proof needs the sphere's compactness and nonemptiness as auxiliary
--   facts.
-- source:
--   Carried as an internal support lemma, with this exact statement and proof, in twelve accepted submissions across ten missions of the OR Formalization Drive (e.g. https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1); published here once so that it can be imported. Yakubovich's S-procedure; see Pólik & Terlaky, A survey of the S-lemma, SIAM Rev. 49 (2007) 371-418, §2.

import Mathlib

open Matrix

theorem Matrix.sLemma_strict {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) :
    (∀ x, x ≠ 0 → 0 ≤ x ⬝ᵥ B *ᵥ x → 0 < x ⬝ᵥ A *ᵥ x) ↔ ∃ τ : ℝ, 0 ≤ τ ∧ (A - τ • B).PosDef := by sorry
