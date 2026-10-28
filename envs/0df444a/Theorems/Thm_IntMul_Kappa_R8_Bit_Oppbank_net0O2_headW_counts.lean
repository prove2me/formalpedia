-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_counts
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_counts
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:30:43.513991+00:00
-- url     : https://prove2.me/theorems/043acbd2-19de-4a8f-bdd6-0b63ec80727a
-- title:
--   OneRun2 head-width multiplicities match oppbankHist
-- statement:
--   For every width $w$, the number of edges of $\mathrm{net0O}$ whose one-run head-width equals $w$ matches the locked opposite-bank histogram multiplicity $n_w(\mathrm{oppbankHist})$.
--
--   This is the GenCN/SideRanks rank-multiset identity feeding `net0O2_oneRunV_oppbank` / `WidthsEqOppbank`.
--
--   **Formalization Note.** Uses `Option.map`/`getD` and `decide` (no center-dot / pipe syntax) for `List.filter : α → Bool`.
-- source:
--   Jain bit_hist.onerun_hist; Hist cb4b257b; GenCN 89952c1f; SideRanks 3ff13a77; OneRun2 e0d447f6

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

theorem net0O2_headW_counts (w : ℕ) :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = w))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = w))).map (fun p => p.2)).sum := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
