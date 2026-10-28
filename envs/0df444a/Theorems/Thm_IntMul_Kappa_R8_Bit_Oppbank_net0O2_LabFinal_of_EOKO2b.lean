-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_LabFinal_of_EOKO2b
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabFinal_of_EOKO2b
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:49:03.376189+00:00
-- url     : https://prove2.me/theorems/31e9fe0b-eea2-43f3-8239-f295da8aee04
-- title:
--   EOKO2 implies final swapMat labels on net0O
-- statement:
--   ### Final frame labels from EOKO (public)
--
--   Under EOKO at field size $N$, densified `net0O` sends every role $\rho(w)$ to $\mathsf{swapMat}$.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace IntMul.Kappa.R8.Bit.Oppbank
open AModel (swapMat)
open IntMul.Kappa.R6.Bit (labStepH)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
theorem net0O2_LabFinal_of_EOKO2b (N : ℕ) (h : EOKO ch0NB N) :
    ∀ w, net0O.prog.foldl (labStepH N) (fun _ => 1) (.inl (net0O.ρ w)) = swapMat := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
