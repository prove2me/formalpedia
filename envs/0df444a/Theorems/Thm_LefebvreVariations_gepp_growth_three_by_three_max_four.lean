-- Prove2me | Theorems.Thm_LefebvreVariations_gepp_growth_three_by_three_max_four
-- name    : LefebvreVariations.gepp_growth_three_by_three_max_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:28:35.355307+00:00
-- url     : https://prove2.me/theorems/745764ea-202a-45a6-b9c3-64b04e9870d3
-- title:
--   Lefebvre's variations, No. 276 — on a theme by Spielman and Yu: partial pivoting on 3 by 3 matrices has growth factor at most 4, attained by Wilkinson's matrix
-- statement:
--   Let $U(A)$ be the upper-triangular matrix produced by Gaussian elimination with partial pivoting on a real $3\times3$ matrix $A$ (pivot of largest modulus in the current column, smallest index on ties), and let $\rho(A)=\max|U(A)|/\max|A|$ be its growth factor, with $\rho(0)=0$. Then
--   $$
--   \rho(A)\le 4\quad\text{for every real } 3\times3\ A,
--   \qquad\text{and}\qquad
--   \rho\!\begin{pmatrix}1&0&1\\-1&1&1\\-1&-1&1\end{pmatrix}=4 ,
--   $$
--   the elimination turning that matrix into $U=\begin{pmatrix}1&0&1\\0&1&2\\0&0&4\end{pmatrix}$.
--
--   Partial pivoting keeps every multiplier of modulus at most $1$, which bounds the growth by $2^{n-1}$ on $n\times n$ matrices, and Wilkinson's matrix attains this bound. How large the growth factor is for random (Gaussian) matrices is the subject of the parent problem; the statement here fixes the worst case for $n=3$.
--
--   **Formalization Note** `growth`, `upper` and `Mat` are the definitions of the parent `GEPPGrowth.Main` (imported from its definitions). The matrix is written `!![1, 0, 1; -1, 1, 1; -1, -1, 1] : Mat 3`. On the zero matrix `growth` is `0 / 0 = 0` in Lean. The conjunction states both the universal bound and that it is attained.
--
--   **Why this is a variation.** A variation on the open platform problem GEPPGrowth.Main.large_growth_probability (Theorem 2.2 of Spielman and Yu on the probability of large growth of Gaussian elimination with partial pivoting for Gaussian matrices, n >= 122). It uses the parent's own definition `growth`, at n = 3, to fix the deterministic worst case 2^(n-1) = 4 and show it is attained. It is context for the parent, not a formal consequence of it.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. H. Wilkinson, Error analysis of direct methods of matrix inversion, J. ACM 8 (1961), for the 2^(n-1) bound and the extremal matrix (cited from memory, pages not verified). Checked here with exact rational arithmetic, simulating the parent's definitions literally (smallest-index tie rule, final U on and above the diagonal): the displayed matrix gives U with rows (1,0,1), (0,1,2), (0,0,4) and growth exactly 4; all 1953125 integer matrices with entries in {-2,...,2} have growth at most 4 (maximum exactly 4), and 200000 random rational matrices stay below 4. The bound itself is the classical consequence of multipliers of modulus at most 1.

import Definitions.Def_GEPPGrowth_Main_Process

set_option autoImplicit false

namespace LefebvreVariations

open GEPPGrowth.Main

/-- Gaussian elimination with partial pivoting on `3 × 3` real matrices: the growth factor of the final `U` (Definition 2.1 of the parent paper) is at most `4 = 2^{n-1}`, and the value `4` is reached by the Wilkinson matrix with rows `(1, 0, 1)`, `(-1, 1, 1)`, `(-1, -1, 1)`, whose `U` has rows `(1, 0, 1)`, `(0, 1, 2)`, `(0, 0, 4)`.
Source: J. H. Wilkinson, *Error analysis of direct methods of matrix inversion*, J. ACM 8 (1961) (cited from memory). -/
theorem gepp_growth_three_by_three_max_four :
    (∀ A : Mat 3, growth A ≤ 4) ∧
      growth (!![1, 0, 1; -1, 1, 1; -1, -1, 1] : Mat 3) = 4 := by
  sorry

end LefebvreVariations
