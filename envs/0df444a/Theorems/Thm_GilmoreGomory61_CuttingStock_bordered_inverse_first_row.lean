-- Prove2me | Theorems.Thm_GilmoreGomory61_CuttingStock_bordered_inverse_first_row
-- name    : GilmoreGomory61.CuttingStock.bordered_inverse_first_row
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:10:29.737276+00:00
-- url     : https://prove2.me/theorems/ec272245-4196-42e7-b838-b929fedc1425
-- title:
--   pp. 852, 854–855 — first row of B inverse and the current tableau column
-- statement:
--   For an invertible basic matrix $A$ with cost row $C$, the paper's bordered matrix satisfies
--
--   $$
--   B^{-1}=\begin{pmatrix}1&C A^{-1}\\0&A^{-1}\end{pmatrix}.
--   $$
--
--   Consequently its first-row multipliers are $b=C A^{-1}$; the first entry of $B^{-1}P$ for any activity or surplus column is $b\cdot a-c$; and the current basic solution costs the first entry of $\bar N=B^{-1}N'$ and satisfies every demand equation with its remaining entries.
--
--   This records the tableau identities that make both the pricing test and the final cost report meaningful.
--
--   **Formalization Note** The initial bordered coordinate is the cost row. A zero-based demand index $i$ denotes the paper's row $i+1$. Invertibility alone suffices; basic feasibility is not assumed.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), p. 852, after (5); p. 854, step (4), continuing on p. 855

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

namespace GilmoreGomory61.CuttingStock

/-- The first row of B⁻¹, the pricing multipliers, and the current N̄ column, pp. 852, 854–855. -/
theorem bordered_inverse_first_row {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsUnit (basisMat I β).det) :
    (bordered I β)⁻¹ =
      Matrix.fromBlocks 1
        (Matrix.of fun _ r => (Matrix.vecMul (costRow I β) (basisMat I β)⁻¹) r)
        0 (basisMat I β)⁻¹ ∧
    mult I β = Matrix.vecMul (costRow I β) (basisMat I β)⁻¹ ∧
    (∀ j : Col I, priceOut I β j =
      (∑ i, mult I β i * colVec I j i) - colCost I j) ∧
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) ∧
    (∀ i, ((basicSol I β).sum fun j v => colVec I j i * v) = (I.N i : ℝ)) := by sorry

end GilmoreGomory61.CuttingStock
