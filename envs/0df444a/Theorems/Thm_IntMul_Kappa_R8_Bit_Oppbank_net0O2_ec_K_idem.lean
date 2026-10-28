-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_K_idem
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ec_K_idem
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:13:42.20058+00:00
-- url     : https://prove2.me/theorems/d67188b2-ba2c-414a-97c6-031d37ff11c0
-- title:
--   Idempotence of ec residual $K(\mathrm{Pl},\mathrm{Pl})$
-- statement:
--   For in-range $(a,s)$, the correction residual $q=K(S_0,S_i,\mathrm{Pl}(a),\mathrm{Pl}(s))$ is idempotent. Feeds `oneRun1_of_piv` for `net0O2_ec_PE`.
--
--   **Formalization Note.** Uses $\mathrm{Pl}$ idempotent and $S_0 S_i=1$.
-- source:
--   supports net0O2_ec_PE via OneRunPE2.oneRun1_of_piv

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_ec_K_idem (a s : ℕ) (ha : a < v) (hs : s < v) :
    K S0 Si0 (Pl a) (Pl s) * K S0 Si0 (Pl a) (Pl s) = K S0 Si0 (Pl a) (Pl s) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
