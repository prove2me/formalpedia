-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_sc_prog
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_prog
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:05:41.938734+00:00
-- url     : https://prove2.me/theorems/6bf210b6-4534-4b7c-b0f6-30a77fa87bbe
-- title:
--   Densified scalar routing for net0O (R6 sc_prog retarget)
-- statement:
--   ### Densified scalar routing
--
--   For the OneRun2 densified network `net0O` over $\mathbb{Z}/2\mathbb{Z}$, the scalar circuit (XOR gates only; edges ignored) sends each initial role value $v(w)$ to the wire $\rho(w)$:
--
--   $$\mathsf{foldl}(\mathsf{scalarStepH},\,v\oplus 0,\,\rho(w))=v(w).$$
--
--   This is the R8 wire-layout retarget of R6 `NB.sc_prog` / block scalar identities.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (scalarStepH)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
theorem net0O2_sc_prog (v : Fin 104719230 → ZMod 2) (w : Fin 104719230) :
    net0O.prog.foldl scalarStepH (Sum.elim v fun _ => 0) (.inl (net0O.ρ w)) = v w := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
