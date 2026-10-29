-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pickE_oneRun_headW
-- name    : IntMul.Kappa.R8.Bit.Oppbank.pickE_oneRun_headW
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:58:08.231867+00:00
-- url     : https://prove2.me/theorems/fef6ce97-e648-457c-9576-3bfdebc60cc9
-- title:
--   pickE of a oneRun-r PE has head-width r
-- statement:
--   If a one-run predicate $\mathrm{PE}(q,\mathrm{oneRun}\,r)$ is inhabited, then the classical choice $\mathrm{pickE}$ returns an edge whose head-run width is exactly $r$:
--   $$
--   \bigl(\exists e,\,\mathrm{PE}(q,\mathrm{oneRun}\,r)\,e\bigr)\implies w\bigl(\mathrm{pickE}(\mathrm{PE}(q,\mathrm{oneRun}\,r))\bigr)=r.
--   $$
--
--   **Formalization Note.** `Classical.choose` of a PE witness; `oneRun r rs` forces `rs=[(0,0,r)]`.
-- source:
--   OneRun2 pickE/PE/oneRun; Classical.choose

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open Matrix
theorem pickE_oneRun_headW (q : Matrix (Fin 529) (Fin 529) ℚ) (r : ℕ)
    (h : ∃ e, PE q (oneRun r) e) :
    (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2)
      (pickE (PE q (oneRun r))).runs.head?).getD 0 = r := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
