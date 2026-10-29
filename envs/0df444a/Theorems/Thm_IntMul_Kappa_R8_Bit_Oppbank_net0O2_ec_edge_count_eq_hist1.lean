-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_edge_count_eq_hist1
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ec_edge_count_eq_hist1
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:50:32.703581+00:00
-- url     : https://prove2.me/theorems/3e0e032f-f5a9-493c-a30e-83c547292adb
-- title:
--   Width-1 edge count equals 221936407
-- statement:
--   The number of edges of $\mathrm{net0O}$ with one-run head-width $1$ is exactly $221936407$, the locked $n_1$ entry of $\mathrm{oppbankHist}$.
--   $$
--   \#\{e:\,w(e)=1\}=221936407.
--   $$
--   This is the numerical form of `net0O2_headW_ec_width1`.
--
--   **Formalization Note.** Concrete Nat equality; hist lookup discharged by `decide`.
-- source:
--   Hist cb4b257b; OneRun2 ec; headW_ec_width1 863e4332

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

theorem net0O2_ec_edge_count_eq_hist1 :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 1))).length =
      221936407 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
