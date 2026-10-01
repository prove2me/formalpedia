-- Prove2me | Theorems.Thm_HlawkaSchatten_SchattenSharpness_cyclic_bound256
-- name    : HlawkaSchatten.SchattenSharpness.cyclic_bound256
-- status  : Open
-- author  : @savarin
-- created : 2026-10-01T04:32:02.208992+00:00
-- url     : https://prove2.me/theorems/d897cb43-a38c-4a3b-b9cd-211dab9660a0
-- title:
--   The cyclic Hlawka bound for all complex operators when p ≥ 256
-- statement:
--   Let $E$ and $F$ be finite-dimensional complex inner-product spaces.
--   A complex-linear map $A:E\to F$ is represented, after choosing
--   orthonormal bases, by a possibly rectangular complex matrix. Its
--   **singular values** $s_i(A)$ are the nonnegative square roots of the
--   eigenvalues of $A^*A$, with zeros permitted. For real $p>1$, its
--   **Schatten norm** is
--   $$
--   N_p(A)=\left(\sum_i s_i(A)^p\right)^{1/p}.
--   $$
--   The finite sum and its outer root are the existing `schattenPNorm`
--   definition. No normalization by dimension is used.
--   [Formal definition](https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/SchattenNorm.lean)
--
--   For maps $A,B,C:E\to F$, define the **triple deficit** and
--   **pair-deficit sum** by
--   $$
--   \Delta_3=N_p(A)+N_p(B)+N_p(C)-N_p(A+B+C),
--   $$
--   $$
--   \Delta_2=2\bigl(N_p(A)+N_p(B)+N_p(C)\bigr)
--   -N_p(A+B)-N_p(A+C)-N_p(B+C).
--   $$
--   An admissible Hlawka constant $K$ satisfies
--   $\Delta_3\le K\Delta_2$ for all such maps.
--
--   The **cyclic candidate** is the real number
--   $$
--   K_p=\sup_{1/2\le t\le2}
--   \frac{3(t^p+2)^{1/p}-3^{1/p}|2-t|}
--   {6(t^p+2)^{1/p}-3(2|1-t|^p+2^p)^{1/p}}.
--   $$
--   It is the existing `DiagonalConstruction.cyclicConstant`, derived
--   from the coordinate triple $(-t,1,1),(1,-t,1),(1,1,-t)$.
--   The supremum is attained and its defining denominator is positive
--   for $p>1$ on the displayed interval.
--   [Cyclic definition and attainment](https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Cyclic.lean)
--
--   The conjecture asks for
--   $$
--   \forall p\ge256,\ \forall E,F,\ \forall A,B,C:E\to_{\mathbb C}F,
--   \qquad \Delta_3\le K_p\Delta_2,
--   $$
--   where $E,F$ range over all finite-dimensional complex inner-product spaces.
--   Their dimensions may differ or be zero. No positivity, commutativity, common
--   diagonalization or equal-norm hypothesis is imposed. The real exponent is
--   arbitrary in the stated tail, not restricted to integers.
-- source:
--   Conjecture motivated by Audenaert–Kittaneh, Problem 7, https://arxiv.org/abs/1201.5232; proved diagonal case: https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ComplexTransfer.lean#L83

import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.SchattenSharpness.cyclic_bound256
    (p : ℝ) (hp : 256 ≤ p)
    (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] :
    HasHlawkaConstant (schattenPNorm p : (E →ₗ[ℂ] F) → ℝ)
      (cyclicConstant p) := by sorry
