-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_ei_edge_count_eq_hist22
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ex_ei_edge_count_eq_hist22
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:51:42.97957+00:00
-- url     : https://prove2.me/theorems/b6b2bd9b-7edf-4b4c-917f-f850a1d6e102
-- title:
--   Width-22 edge count equals 116886
-- statement:
--   The number of edges of $\mathrm{net0O}$ with one-run head-width $22$ is exactly $116886$, matching $n_{22}(\mathrm{oppbankHist})$.
--   $$
--   \#\{e:\,w(e)=22\}=116886.
--   $$
--
--   **Formalization Note.** Concrete Nat equality.
-- source:
--   Hist; OneRun2; headW fixed width 22

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
theorem net0O2_ex_ei_edge_count_eq_hist22 :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 22))).length =
      116886 := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
