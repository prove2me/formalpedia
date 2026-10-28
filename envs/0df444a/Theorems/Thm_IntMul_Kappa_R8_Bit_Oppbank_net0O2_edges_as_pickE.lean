-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_as_pickE
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_edges_as_pickE
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:54:51.949227+00:00
-- url     : https://prove2.me/theorems/4354a25f-86ed-4abd-a333-09351d1c4164
-- title:
--   Every net0O edge is pickE of an inhabited oneRun PE
-- statement:
--   Every edge of the corrected one-run network is obtained as `pickE` of an inhabited one-run edge predicate $\mathrm{PE}(q,\mathrm{oneRun}(r))$ for some residual matrix $q$ and width $r$. Combined with `net0O2_pickE_oneRun` this yields `net0O2_edges_oneRun`.
--
--   The residual $q$ ranges over the Six OneRun2 families (`e1`/`e2`/`ex`/`en`/`ei`/`ec`) from `ch0O`.
--
--   **Formalization Note.** Structural consequence of `NB.net`/`progEdges` on `ch0O`; PE inhabitance supplied by the family leaves.
-- source:
--   OneRun2 ch0O/net0O; PE families e1/e2/ex/en/ei/ec; pickE_oneRun 0397d57f

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open Matrix

theorem net0O2_edges_as_pickE :
    ∀ e ∈ net0O.edges,
      ∃ (r : ℕ) (q : Matrix (Fin 529) (Fin 529) ℚ),
        (∃ e', PE q (oneRun r) e') ∧ e = pickE (PE q (oneRun r)) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
