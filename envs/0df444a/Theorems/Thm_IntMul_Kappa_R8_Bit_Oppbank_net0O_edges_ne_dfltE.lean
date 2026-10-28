-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_edges_ne_dfltE
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O_edges_ne_dfltE
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:04:43.633778+00:00
-- url     : https://prove2.me/theorems/b619c27e-6b2e-4421-91a4-0146c54fe84f
-- title:
--   net0O.edges contains no default residual
-- statement:
--   # No default edges in net0O
--
--   Every edge of $\mathrm{net0O}$ is a true one-run \`pickE\` (not \`dfltE\`). Follows from channel PE inhabitance (\`PE_pos\` family).
-- source:
--   edges_as_pickE

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

theorem net0O_edges_ne_dfltE : ∀ e ∈ net0O.edges, e ≠ dfltE := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
