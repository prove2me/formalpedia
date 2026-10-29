-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entE_grid_all_width484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_entE_grid_all_width484
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:23:46.667536+00:00
-- url     : https://prove2.me/theorems/baf89074-35e2-4da1-aefd-41c93ed8d11f
-- title:
--   Every entE-grid edge has head-width 484
-- statement:
--   Every densified entrance edge in the stage-two grid has one-run head-width $484$: for each block index $a<v$ and each local wire $w<w_{\mathrm{Ent}}$,
--   $$
--   w\bigl(\mathrm{entE}(a,w)\bigr)=484.
--   $$
--   This is the pointwise form of `entE_width484` on the flatmapped grid list.
--
--   **Formalization Note.** Membership in `(List.range v).flatMap (a ↦ (List.range wEnt).map (entE a))`.
-- source:
--   OneRun2 entE grid; mom en cascade

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_entE_grid_all_width484 :
    ∀ e ∈ ((List.range v).flatMap fun a =>
        (List.range wEnt).map fun w => NB.entE (toNB ch0O) a w),
      (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484 := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
