-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oneRunV_sum_counts
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_oneRunV_sum_counts
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:38:51.605979+00:00
-- url     : https://prove2.me/theorems/bc9e5801-c707-407c-be44-464fb63640ae
-- title:
--   oneRunV edge sum equals weighted oppbankCount sum
-- statement:
--   The sum of one-run edge moments over $\mathrm{net0O}$ equals the histogram expansion of $\mathrm{oppbankHist}$:
--   $$
--   \sum_{e}\mathrm{oneRunV}_\tau(w(e))
--   =
--   \sum_{(w,n_w)\in\mathrm{oppbankHist}} n_w\cdot\mathrm{oneRunV}_\tau(w).
--   $$
--   This is the multiplicity form of `net0O2_oneRunV_oppbank` (since $\mathrm{histMoment}=\sum n_w(w/529)^\tau$ and $\mathrm{oneRunV}_\tau(w)=(w/529)^\tau$). Discharged by `net0O2_headW_counts` plus partitioning the edge list by head-width.
--
--   **Formalization Note.** Uses explicit `Option.map` (no center-dot) for head-width.
-- source:
--   Jain bit_hist.onerun_hist; headW_counts 043acbd2; OneRunMom2 a4deb37c

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2

theorem net0O2_oneRunV_sum_counts (τ : ℝ) :
    (net0O.edges.map fun e =>
        oneRunV τ ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0)).sum =
      (oppbankHist.map fun p => (p.2 : ℝ) * oneRunV τ p.1).sum := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
