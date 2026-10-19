-- Prove2me | Theorems.Thm_HlawkaSchatten_SchattenSharpness_realSymmetric_cyclic_bound256
-- name    : HlawkaSchatten.SchattenSharpness.realSymmetric_cyclic_bound256
-- status  : Open
-- author  : @savarin
-- created : 2026-10-16T23:52:29.182906+00:00
-- url     : https://prove2.me/theorems/f23e26b6-a96a-4703-a78f-9238713ef33a
-- title:
--   The cyclic Hlawka bound for real symmetric operators when p ≥ 256
-- statement:
--   Let $H$ be a finite-dimensional real inner-product space, of any dimension. A linear map $A:H\to H$ is **symmetric** if $\langle Ax,y\rangle=\langle x,Ay\rangle$ for all $x,y\in H$; in an orthonormal basis it is a real symmetric matrix. For real $p>1$ its **Schatten norm** is
--
--   $$
--   N_p(A)=\Bigl(\sum_i s_i(A)^p\Bigr)^{1/p},
--   $$
--
--   where $s_i(A)$ are the singular values of $A$; for symmetric $A$ they are the absolute values of its eigenvalues, counted with multiplicity. This is the existing `schattenPNorm` definition, with no normalization by dimension.
--
--   For symmetric $A,B,C:H\to H$, the **triple deficit** and the **pair-deficit sum** are
--
--   $$
--   \Delta_3=N_p(A)+N_p(B)+N_p(C)-N_p(A+B+C),
--   $$
--
--   $$
--   \Delta_2=2\bigl(N_p(A)+N_p(B)+N_p(C)\bigr)-N_p(A+B)-N_p(A+C)-N_p(B+C),
--   $$
--
--   and the **cyclic constant** is the existing `DiagonalConstruction.cyclicConstant`,
--
--   $$
--   K_p=\sup_{1/2\le t\le2}\frac{3(t^p+2)^{1/p}-3^{1/p}|2-t|}{6(t^p+2)^{1/p}-3(2|1-t|^p+2^p)^{1/p}}.
--   $$
--
--   **Statement.** For every real $p\ge256$, every finite-dimensional real inner-product space $H$ and all symmetric $A,B,C:H\to H$,
--
--   $$
--   \Delta_3\le K_p\,\Delta_2 .
--   $$
--
--   This is the real symmetric case of `HlawkaSchatten.SchattenSharpness.selfAdjoint_cyclic_bound256`, and it is equivalent to it: a complex self-adjoint operator, viewed as a real-linear map with inner product $\mathrm{Re}\langle x,y\rangle$, is symmetric with every singular value repeated twice, so $N_p$ is multiplied by $2^{1/p}$; conversely, complexifying a real symmetric operator keeps every singular value with its multiplicity. The self-adjoint statement is itself equivalent to the general-matrix conjecture `HlawkaSchatten.SchattenSharpness.cyclic_bound256` through the Hermitian dilation, which carries every rectangular operator to a self-adjoint one and multiplies $N_p$ by $2^{1/p}$. A proof of the present statement therefore proves that conjecture.
--
--   **Formalization Note.** Symmetry is Mathlib's `LinearMap.IsSymmetric` over $\mathbb R$. The space $H$ may have any finite dimension, including $0$, $1$ and $2$. No positivity, commutativity, common-eigenbasis or equal-norm hypothesis is imposed.
-- source:
--   Real symmetric case of HlawkaSchatten.SchattenSharpness.selfAdjoint_cyclic_bound256 (https://prove2.me/theorems/ce816d92-eaf6-404f-b7ea-effee7e7aeb5), which is the self-adjoint case of the conjecture HlawkaSchatten.SchattenSharpness.cyclic_bound256 (https://prove2.me/missions/Does_the_sharp_diagonal_Hlawka_constant_work_for_all_complex_matrices_when_p_%E2%89%A5_256%3F), motivated by Audenaert–Kittaneh, Problems and Conjectures in Matrix and Operator Inequalities, §8.2, Problem 7 (inequality (48), p. 12 of arXiv v3), https://arxiv.org/abs/1201.5232; proved diagonal case: https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ComplexTransfer.lean#L83

import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.SchattenSharpness.realSymmetric_cyclic_bound256
    (p : ℝ) (hp : 256 ≤ p)
    (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (A B C : H →ₗ[ℝ] H)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hC : C.IsSymmetric) :
    tripleGap (schattenPNorm p : (H →ₗ[ℝ] H) → ℝ) A B C ≤
      cyclicConstant p * pairGapSum (schattenPNorm p : (H →ₗ[ℝ] H) → ℝ) A B C := by sorry
