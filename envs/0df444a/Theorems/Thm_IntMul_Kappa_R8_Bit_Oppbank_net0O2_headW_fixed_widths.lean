-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_fixed_widths
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_fixed_widths
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:36:18.897734+00:00
-- url     : https://prove2.me/theorems/cb324006-fa9d-44f9-9ea8-87a83125d845
-- title:
--   Fixed-width edge counts (1, 22, 484) match oppbankHist
-- statement:
--   Among the edges of $\mathrm{net0O}$, the multiplicities of the fixed one-run widths $w\in\{1,22,484\}$ (from the $e_c$, $e_x$/$e_i$, and $e_n$ families) equal the corresponding entries of $\mathrm{oppbankHist}$.
--   $$
--   \#\{e:\,w(e)=w\}=n_w(\mathrm{oppbankHist})\qquad(w\in\{1,22,484\}).
--   $$
--   This is the fixed-width half of `net0O2_headW_from_PE_pack`.
--
--   **Formalization Note.** Uses `decide` filters as in `headW_counts`.
-- source:
--   OneRun2 ch0O ex/ei/en/ec; Hist cb4b257b; headW_from_PE_pack e396af7c

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

theorem net0O2_headW_fixed_widths (w : ℕ) (hw : w = 1 ∨ w = 22 ∨ w = 484) :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = w))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = w))).map (fun p => p.2)).sum := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
