-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_slots_count
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_slots_count
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:17:53.370566+00:00
-- url     : https://prove2.me/theorems/5d7f7a68-ca74-47b9-bae0-dc259b6c566c
-- title:
--   Width-484 edge count equals 1771 · 3542
-- statement:
--   The number of edges of $\mathrm{net0O}$ with one-run head-width $484$ equals $1771\cdot 3542$. These are exactly the densified data-entrance $e_n$ slots: for each of the $v=1771$ stage-two blocks and each local wire $w<w_{\mathrm{Ent}}=3542$, the entrance edge uses an $e_n$ child of width $484$.
--   $$
--   \#\{e:\,w(e)=484\}=1771\cdot 3542.
--   $$
--
--   **Formalization Note.** Uses OneRun2 `net0O`. The arithmetic identity $1771\cdot 3542=6272882$ is discharged by `decide` / `net0O2_v_mul_wEnt`.
-- source:
--   OneRun2; QHNet entI; bit_hist data entrance 2N

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

theorem net0O2_en_slots_count :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))).length =
      1771 * 3542 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
