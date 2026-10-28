-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_channel_pickE
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_edges_channel_pickE
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:10:57.89578+00:00
-- url     : https://prove2.me/theorems/17eea5af-9920-4980-8e14-61e38e87e5ba
-- title:
--   Every net0O edge is a channel pickE or default
-- statement:
--   # Channel form of one-run network edges
--
--   Every edge in $\mathrm{net0O}.\mathrm{edges}$ is either `OneRunNet2.dfltE` or a channel `pickE` of a one-run PE predicate among the six opp-bank families. Enables `AllOneRun` without universal PE inhabitance.
--
--   **Formalization Note.** Disambiguates `Pnd.dfltE`/`PE` vs `OneRunNet2` (prior submit FAILED on ambiguity).
-- source:
--   BitNB OneRun2 mom-path; AllOneRun support

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_edges_channel_pickE :
    ∀ e ∈ net0O.edges,
      e = OneRunNet2.dfltE ∨
        (∃ b o c, b < v ∧ o < codeBound ∧ c < codeBound ∧
          e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Dm o c) (Pl b)) (oneRun (rkC o c)))) ∨
        (∃ a o c, a < v ∧ o < codeBound ∧ c < codeBound ∧
          e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Pl a) (Dm o c)) (oneRun (rkC o c)))) ∨
        (∃ b, b < v ∧ e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 1 (1 - Pl b)) (oneRun 22))) ∨
        (∃ a, a < v ∧ e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22))) ∨
        (∃ a t, a < v ∧ t < v ∧
          e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484))) ∨
        (∃ a s, a < v ∧ s < v ∧
          e = OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (Pl a) (Pl s)) (oneRun 1))) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
