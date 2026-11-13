-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_nuGridSupply_swap
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.nuGridSupply_swap
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:41:17.816667+00:00
-- url     : https://prove2.me/theorems/4f43a3d5-be28-4ba4-b397-b81e68c6c743
-- title:
--   Peterfalvi (13.1.e)/(4.3)-(4.9): the swapped hypothesis again supplies the $\nu$-grid data
-- statement:
--   Let $G$ be a finite group and `hyp` a Peterfalvi §13 configuration for $G$ (`OddOrder.Peterfalvi.S15.Hypothesis`). Assume:
--
--   - $V$ (`hyp.V`) is commutative (`IsMulCommutative ↥hyp.V`);
--   - `Tdata : TypePData hyp.T` is a type-$P$ datum for $T$ with $U$-component equal to $V$ (`Tdata.U = hyp.V`) and with $W_1$-, $W_2$-components equal to $W_2$ and $W_1$ of `hyp` respectively (`Tdata.W1 = hyp.W2`, `Tdata.W2 = hyp.W1`);
--   - `pins : NuGridSupplyData hyp` is the data supplying the $\nu$-grid fields for `hyp`.
--
--   Then the swapped configuration `hyp.swap hV Tdata hU hW1 hW2 pins` again carries `NuGridSupplyData`, i.e.
--   $$\texttt{NuGridSupplyData}\ \bigl(\texttt{hyp.swap}\ \cdots\bigr)\ \text{holds (is inhabited)}.$$
--
--   This allows the $p \leftrightarrow q$ symmetry of the §13 configuration (exchanging the roles of $S$ and $T$) to be applied a second time. Transposing the original $\mu$-grid fields supplies each $\nu$-grid field of the doubly swapped hypothesis.
--
--   **Formalization Note.** `NuGridSupplyData hyp` is a project-defined bundled structure of $\nu$-grid fields; the statement produces a term of that structure for the swapped hypothesis.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/SwappedNuGridSupply.lean#L26-L70

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open scoped FiniteInduce

variable {G : Type*} [Group G]

section

theorem Hypothesis.nuGridSupply_swap [Finite G]
    (hyp : Hypothesis (G := G))
    (hV : IsMulCommutative ↥hyp.V)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (pins : NuGridSupplyData hyp) :
    NuGridSupplyData (hyp.swap hV Tdata hU hW1 hW2 pins) := by sorry

end

end OddOrder.Peterfalvi.S15
