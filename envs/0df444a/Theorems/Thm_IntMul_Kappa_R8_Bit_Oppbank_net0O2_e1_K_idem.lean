-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_K_idem
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_e1_K_idem
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:07:26.662463+00:00
-- url     : https://prove2.me/theorems/228c2a0f-44c6-4ff0-a92c-011fa02bb918
-- title:
--   Idempotence of e1 residual $K(\mathrm{Dm},\mathrm{Pl})$
-- statement:
--   # Idempotence of the stage-one densified residual
--
--   For in-range $(b,o,c)$ with $r=\mathrm{rkC}(o,c)>0$, the conjugated Kronecker residual
--   $$
--   q = K(S_0,S_i,\mathrm{Dm}(o,c),\mathrm{Pl}(b)) = S_0\,(\mathrm{Dm}(o,c)\otimes_k \mathrm{Pl}(b))\,S_i
--   $$
--   is an idempotent matrix: $q^2=q$. This is the first hypothesis of `OneRunPE2.oneRun_of_pivs`.
--
--   **Formalization Note.** Downstream of FB0 / projector idempotence (`Dm`, `Pl`) and $S_0 S_i=1$.
-- source:
--   BitNB OneRun2 mom-path 2026-10-29; supports net0O2_e1_PE_pos / AllOneRun

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_e1_K_idem (b o c : ℕ) (hb : b < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    let q := K S0 Si0 (Dm o c) (Pl b)
    q * q = q := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
