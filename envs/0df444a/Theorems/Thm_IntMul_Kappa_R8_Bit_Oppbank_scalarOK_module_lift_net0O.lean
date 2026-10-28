-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_scalarOK_module_lift_net0O
-- name    : IntMul.Kappa.R8.Bit.Oppbank.scalarOK_module_lift_net0O
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:10:28.001277+00:00
-- url     : https://prove2.me/theorems/b867cf68-54f9-44ff-9efb-85153fab9ed3
-- title:
--   ScalarOK lifts to formal-value wires on net0O
-- statement:
--   ### Module lift of ScalarOK
--
--   Given `ScalarOK` for densified `net0O`, the same routing holds with formal values as the coefficient module: $f_{\mathrm{Init}}$ is sent to $\mathbf{1}_{(I,w)}$ at $\rho(w)$. Freeness of the formal-value module / naturality of `scalarStepM` vs `scalarStepH`.

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
theorem scalarOK_module_lift_net0O (N : ℕ)
    (hS : ScalarOK (m := 529) (R := ZMod 2) net0O) (w : Fin 104719230) :
    net0O.prog.foldl (scalarStepM (R := ZMod 2) (M := FV (ZMod 2) (Fin 104719230) 529 N))
      (fInit (R := ZMod 2) (m := 529) N) (.inl (net0O.ρ w)) =
      Finsupp.single ((1 : FMat 529 N), w) 1 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
