-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_cs1_locals_lt_NL
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_cs1_locals_lt_NL
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:49:09.376297+00:00
-- url     : https://prove2.me/theorems/67d58505-a798-4261-83f1-37feecaab361
-- title:
--   Local wire endpoints of cs1 lie strictly below NL
-- statement:
--   Every local wire index that appears as a move or XOR endpoint inside the stage-one chunk list \(\mathrm{cs1}\) is strictly below \(NL=31359\).
--
--   Since \(\mathrm{cs1}=(\mathrm{genF}(\mathrm{codeOf}(SG1_0),W_{1F})).2\), the claim reduces to genF local-preservation plus the \(W_{1F}\) wire bound.
--
--   Formalization Note. Endpoints are first components of \(\mathrm{ch}.2.1\) and both components of \(\mathrm{ch}.2.2\) across \(\mathrm{ch}\in\mathrm{cs1}\).
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: cs1 local bound

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (Instr)
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NL)
theorem net0O2_cs1_locals_lt_NL (ℓ : ℕ)
    (hℓ : ∃ ch ∈ cs1,
      (∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) :
    ℓ < NL := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
