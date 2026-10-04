-- Prove2me | Theorems.Thm_HlawkaSchatten_schattenPNorm_two_hasHlawkaConstant
-- name    : HlawkaSchatten.schattenPNorm_two_hasHlawkaConstant
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T00:03:24.744205+00:00
-- url     : https://prove2.me/theorems/bd56fe3a-73eb-422e-ab36-dd54f1133922
-- title:
--   The Schatten $2$-quantity has Hlawka constant one
-- statement:
--   Let $\mathbb{K}\in\{\mathbb{R},\mathbb{C}\}$, and let $E$ and $F$ be finite-dimensional inner-product spaces over $\mathbb{K}$. For a linear map $T:E\to F$, write $N_2(T)$ for its Schatten $2$-quantity: if $s_i(T)$ are the singular values of $T$, then
--   $$
--   N_2(T)=\Bigl(\sum_i s_i(T)^2\Bigr)^{1/2}.
--   $$
--   For maps $A,B,C:E\to F$, write
--   $$
--   \Delta_3=N_2(A)+N_2(B)+N_2(C)-N_2(A+B+C)
--   $$
--   and
--   $$
--   \Delta_2=2\bigl(N_2(A)+N_2(B)+N_2(C)\bigr)-N_2(A+B)-N_2(A+C)-N_2(B+C).
--   $$
--   Then $N_2$ has Hlawka constant one:
--   $$
--   \Delta_3\le \Delta_2.
--   $$
--   Equivalently,
--   $$
--   N_2(A+B)+N_2(A+C)+N_2(B+C)\le N_2(A)+N_2(B)+N_2(C)+N_2(A+B+C).
--   $$
--
--   This is the case $C_2=1$ of Audenaert–Kittaneh’s Problem 7, the only exponent for which the optimal Schatten Hlawka constant is classical. The same statement is the Hilbert–Schmidt layer of the Schatten development: $N_2$ is the Hilbert norm of the column coordinates of $T$ in any orthonormal basis, so the inner-product Hlawka inequality passes to $N_2$ with constant one. Dimensions of $E$ and $F$ may differ, and either space may be zero.
--
--   **Formalization Note.** $N_2$ is `schattenPNorm 2`, and the claimed bound is `HasHlawkaConstant (schattenPNorm 2) 1`. The scalar field is Mathlib’s `RCLike`.
-- source:
--   Audenaert–Kittaneh, Problem 7, the settled case C_2=1, https://arxiv.org/abs/1201.5232; formal statement and proof: https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HilbertSchmidt.lean#L109-L121

import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten

theorem HlawkaSchatten.schattenPNorm_two_hasHlawkaConstant
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
    HasHlawkaConstant (schattenPNorm 2 : (E →ₗ[𝕜] F) → ℝ) 1 := by sorry
