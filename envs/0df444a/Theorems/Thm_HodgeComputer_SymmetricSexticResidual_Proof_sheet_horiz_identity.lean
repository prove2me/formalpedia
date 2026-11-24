-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_sheet_horiz_identity
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.sheet_horiz_identity
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:53:54.727831+00:00
-- url     : https://prove2.me/theorems/4e4261bc-19ec-4119-b900-230f10f897fc
-- title:
--   Pointwise horizontal sheet divergence identity over finite extensions $L / K_5$
-- statement:
--   Let $L / K_5$ be a finite field extension and $(a, b, U, V) \in L^4$ a nondegenerate solution to the horizontal sheet equations $E_k(S, Q, T, a, b, U, V) = 0$ ($k = 0, 1, 2, 3$) satisfying $U, V \notin \{0, 1\}$, $\det J_{\mathrm{fib}} \neq 0$, and $\det M_{ab,SQ} \neq 0$. Then the horizontal sheet vector `w_horiz a b U V` satisfies
--
--   $$2 W_2 H_0^2 \,\operatorname{resDivW}_L(\operatorname{w\_horiz}(a, b, U, V)) = -\frac{P_{18}(S, Q, T, x, y, a, b, U, V)}{81 \det J_{\mathrm{fib}}(S, Q, T, a, b, U, V)}.$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/SheetCalculus.lean#L1455-L1821

import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_SheetCalculus
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.sheet_horiz_identity
    {L : Type*} [Field L] [CharZero L] [Algebra SymmetricSexticResidual.K5Field.K5 L]
    [FiniteDimensional SymmetricSexticResidual.K5Field.K5 L]
    (a b U V : L)
    (hE : ∀ k : Fin 4, SymmetricSexticResidual.SheetCalculus.E_fn k
      (SymmetricSexticResidual.SheetCalculus.SL (L := L))
      SymmetricSexticResidual.SheetCalculus.QL
      SymmetricSexticResidual.SheetCalculus.TL a b U V = 0)
    (hU0 : U ≠ 0) (hV0 : V ≠ 0) (hU1 : U ≠ 1) (hV1 : V ≠ 1)
    (hJ : (SymmetricSexticResidual.SheetCalculus.J_fib
      (SymmetricSexticResidual.SheetCalculus.SL (L := L))
      SymmetricSexticResidual.SheetCalculus.QL
      SymmetricSexticResidual.SheetCalculus.TL a b U V).det ≠ 0)
    (hM : (SymmetricSexticResidual.SheetCalculus.M_abSQ
      (SymmetricSexticResidual.SheetCalculus.SL (L := L))
      SymmetricSexticResidual.SheetCalculus.QL
      SymmetricSexticResidual.SheetCalculus.TL a b U V).det ≠ 0) :
    2 * SymmetricSexticResidual.SheetCalculus.ιL SymmetricSexticResidual.K5Field.W2_K *
      SymmetricSexticResidual.SheetCalculus.ιL SymmetricSexticResidual.K5Field.H0_K ^ 2 *
      SymmetricSexticResidual.SheetCalculus.resDivW_L (SymmetricSexticResidual.SheetCalculus.w_horiz a b U V) =
      -SymmetricSexticResidual.SheetCalculus.P18_of
        (SymmetricSexticResidual.SheetCalculus.SL (L := L))
        SymmetricSexticResidual.SheetCalculus.QL
        SymmetricSexticResidual.SheetCalculus.TL
        SymmetricSexticResidual.SheetCalculus.xL
        SymmetricSexticResidual.SheetCalculus.yL a b U V /
      (81 * (SymmetricSexticResidual.SheetCalculus.J_fib
        (SymmetricSexticResidual.SheetCalculus.SL (L := L))
        SymmetricSexticResidual.SheetCalculus.QL
        SymmetricSexticResidual.SheetCalculus.TL a b U V).det) := by sorry
