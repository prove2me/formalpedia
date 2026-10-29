-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_rkC_widths
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_rkC_widths
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:35:54.864381+00:00
-- url     : https://prove2.me/theorems/a2f6f1df-c2bc-4fbe-8f0b-ff13c84b2d88
-- title:
--   Variable rkC edge counts match oppbankHist
-- statement:
--   For every width $w\notin\{1,22,484\}$, the number of $\mathrm{net0O}$ edges of head-width $w$ equals $n_w(\mathrm{oppbankHist})$. These arise from the $e_1$/$e_2$ families with residual width $\mathrm{rkC}(o,c)$, counted by GenCN rank packs $\mathrm{DC}$.
--   $$
--   \#\{e:\,w(e)=w\}=n_w(\mathrm{oppbankHist})\qquad(w\notin\{1,22,484\}).
--   $$
--
--   **Formalization Note.** Companion to `net0O2_headW_fixed_widths`.
-- source:
--   GenCN DC; SideRanks; OneRun2 e1/e2; headW_from_PE_pack e396af7c

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

theorem net0O2_headW_rkC_widths (w : ℕ) (hw : w ≠ 1 ∧ w ≠ 22 ∧ w ≠ 484) :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = w))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = w))).map (fun p => p.2)).sum := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
