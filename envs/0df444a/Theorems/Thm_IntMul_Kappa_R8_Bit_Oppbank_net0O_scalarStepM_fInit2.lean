-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_scalarStepM_fInit2
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O_scalarStepM_fInit2
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:51:11.244066+00:00
-- url     : https://prove2.me/theorems/2d6a8b8c-571a-45a6-9fe3-a05ff71388a0
-- title:
--   ScalarOK lifts to formal-value routing on net0O
-- statement:
--   ### Scalar routing on formal values (public leaf)
--
--   Assume `ScalarOK` for densified `net0O`. The module-valued scalar circuit sends $f_{\mathrm{Init}}$ to $\mathbf{1}_{(I,w)}$ at role $\rho(w)$. Public densified NetC leaf for the `formal_labels` bridge.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (FMat FV scalarStepM)
open IntMul.Kappa.R6.Bit.QHNet (ScalarOK fInit)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
theorem net0O_scalarStepM_fInit2 (N : ℕ)
    (hS : ScalarOK (m := 529) (R := ZMod 2) net0O) (w : Fin 104719230) :
    net0O.prog.foldl (scalarStepM (R := ZMod 2) (M := FV (ZMod 2) (Fin 104719230) 529 N))
      (fInit (R := ZMod 2) (m := 529) N) (.inl (net0O.ρ w)) =
      Finsupp.single ((1 : FMat 529 N), w) 1 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
