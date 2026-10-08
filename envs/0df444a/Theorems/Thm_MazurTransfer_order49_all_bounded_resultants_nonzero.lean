-- Prove2me | Theorems.Thm_MazurTransfer_order49_all_bounded_resultants_nonzero
-- name    : MazurTransfer.order49_all_bounded_resultants_nonzero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T21:59:40.613635+00:00
-- url     : https://prove2.me/theorems/20e39e57-2242-49df-8c54-733ff0014cbf
-- title:
--   Order-49 all three bounded resultants are nonzero at every nonsingular parameter
-- statement:
--   Let $G_d,H_{0,d},H_{1,d},H_{2,d}\in\mathbb Q[X]$ be the fixed selection and three division cofactors specialized at $d\in\mathbb Q$. If $d\ne0$, $d\ne1$ and $d^3-8d^2+5d+1\ne0$, then $$\operatorname{Res}_{33,7}(G_d,H_{i,d})\ne0\qquad(i=0,1,2).$$ This provides all three algebraic obstructions used to exclude rational points of order $49$, including specializations where the selection polynomial loses degree.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.bounded_resultants_ne_zero kernel type, verified by applying the original checked theorem with only standard axioms. Original pure cofactor definitions are preserved in the separately published data. This type audit uses the checked source module and is not represented as an uploadable closed transfer. Design boundary and named downstream consumer: All three exact fixed bounded resultants at every nonsingular rational Kubert parameter, without assuming degree preservation after specialization. Full arbitrary-E MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine. No extra arithmetic or torsion assumptions, weakened data, or degree-preservation hypothesis.

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Mathlib.RingTheory.Polynomial.Resultant.Basic

theorem MazurTransfer.order49_all_bounded_resultants_nonzero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0 ∧
    Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0 ∧
    Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0 := by sorry
