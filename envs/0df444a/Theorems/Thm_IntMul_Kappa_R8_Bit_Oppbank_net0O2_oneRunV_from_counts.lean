-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oneRunV_from_counts
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_oneRunV_from_counts
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:20:30.655825+00:00
-- url     : https://prove2.me/theorems/3e5ba56f-173f-432a-89aa-3917d9ae919c
-- title:
--   oneRunV edge sum from multiplicity hypothesis
-- statement:
--   Assume that for every width $w$, the number of edges of $\mathrm{net0O}$ with one-run head-width $w$ equals the multiplicity $n_w$ recorded in $\mathrm{oppbankHist}$. Then
--   $$
--   \sum_{e}\mathrm{oneRunV}_\tau(w(e))=\sum_{(w,n_w)\in\mathrm{oppbankHist}} n_w\cdot\mathrm{oneRunV}_\tau(w).
--   $$
--   This counting bridge discharges `net0O2_oneRunV_sum_counts` once `net0O2_headW_counts` is available.
--
--   **Formalization Note.** Hypothesis mirrors `net0O2_headW_counts`.
-- source:
--   headW_counts 043acbd2; sum_counts bc9e5801; OneRunMom2

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

theorem net0O2_oneRunV_from_counts (τ : ℝ)
    (h : ∀ w : ℕ,
      (net0O.edges.filter
          (fun e : Edge 529 =>
            decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = w))).length =
        ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = w))).map (fun p => p.2)).sum) :
    (net0O.edges.map fun e =>
        oneRunV τ ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0)).sum =
      (oppbankHist.map fun p => (p.2 : ℝ) * oneRunV τ p.1).sum := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
