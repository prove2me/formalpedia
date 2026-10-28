-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_from_PE_pack
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_from_PE_pack
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:23:58.703257+00:00
-- url     : https://prove2.me/theorems/e396af7c-0a7e-4c7e-9b13-7b07b3decb0f
-- title:
--   Head-width counts from PE-family packing
-- statement:
--   The multiplicity of each one-run head-width $w$ among the edges of $\mathrm{net0O}$ equals the locked opposite-bank histogram entry $n_w(\mathrm{oppbankHist})$.
--   $$
--   \#\{e:\,w(e)=w\}=n_w(\mathrm{oppbankHist}).
--   $$
--   Discharged by PE-family width inventories (GenCN/SideRanks) matching Jain `bit_hist.onerun_hist`.
--
--   **Formalization Note.** Same statement shape as `net0O2_headW_counts`; content leaf.
-- source:
--   headW_counts 043acbd2; GenCN 89952c1f; SideRanks 3ff13a77; Hist cb4b257b

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

/-- GenCN / SideRanks / PE-family width packing: head-width multiplicity equals oppbankHist. -/
theorem net0O2_headW_from_PE_pack (w : ℕ) :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = w))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = w))).map (fun p => p.2)).sum := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
