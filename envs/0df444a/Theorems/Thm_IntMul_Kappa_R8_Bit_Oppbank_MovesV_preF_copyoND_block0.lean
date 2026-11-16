-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_MovesV_preF_copyoND_block0
-- name    : IntMul.Kappa.R8.Bit.Oppbank.MovesV_preF_copyoND_block0
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:36:32.892076+00:00
-- url     : https://prove2.me/theorems/01963e13-cfdf-4bdf-8d5c-c03b479b843a
-- title:
--   MovesV/ValidOn for preF ++ copyoND ++ leafMix ++ gateMix from initR (QHNetRecR block-0 prefix)
-- statement:
--   # Block-0 prefix of the variant-R word is a valid nested move
--
--   On the published variant-R carrier, let $\mathrm{initR}$ be the stage-one initial labelling, and let $\mathrm{gateMix}$ be the list of $1301$ block-0 gate mix-forward records (the first block of the mix-forward schedule, $\mathrm{mixFB}(0,12)$). Extending the already-established prefix $\mathrm{preF}{+}\!{+}\mathrm{copyoND}{+}\!{+}\mathrm{leafMix}$ by $\mathrm{gateMix}$ and running the generator from $\mathrm{initR}$ yields a valid labelling whose recorded moves are nested at bound $64251$:
--
--   $$\mathrm{ValidOn}(\mathrm{initR})\ \wedge\ \mathrm{MovesV}\bigl(\mathrm{genF}(\mathrm{initR},\mathrm{preF}{+}\!{+}\mathrm{copyoND}{+}\!{+}\mathrm{leafMix}{+}\!{+}\mathrm{gateMix})\bigr)\ \wedge\ \mathrm{ValidOn}\bigl(\mathrm{genF}(\mathrm{initR},\mathrm{preF}{+}\!{+}\mathrm{copyoND}{+}\!{+}\mathrm{leafMix}{+}\!{+}\mathrm{gateMix})_{1}\bigr).$$
--
--   After the leaf-mix stage, each gate pivot and base slot already carries the corresponding source code, and high slots remain zero, so every recorded block-0 gate move is a well-nested write.
--
--   ## Formalization Note
--
--   The statement is `Lab.ValidOn` / `Lab.MovesV` for `Gen.genF initR (QHNetRecR.preF ++ QHNetRecR.copyoND ++ leafMix ++ gateMix)` at `codeBound = 64251`. It does not unfold `segsR` or `W1F`, and it is not a full-word `MovesV` certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: prefix MovesV/ValidOn for QHNetRecR.preF ++ QHNetRecR.copyoND ++ leafMix ++ gateMix from initR at Lab.codeBound 64251. gateMix is the 1301 block-0 mix-forward records (mixFB 0 12). Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState3a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBData1
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace IntMul.Kappa.R8.Bit.Oppbank

/-- Prefix-only `MovesV` / `ValidOn` certificate for
`preF ++ copyoND ++ leafMix ++ gateMix` from `initR` on the published
variant-R carrier. This does not unfold `segsR` or `W1F`, does not cover
later mix-forward gates or preloads, and is not a full-word `MovesV`
certificate. -/
theorem MovesV_preF_copyoND_block0 :
    Lab.ValidOn initR ∧
      Lab.MovesV (Gen.genF initR (QHNetRecR.preF ++ QHNetRecR.copyoND ++ leafMix ++ gateMix)).2 ∧
        Lab.ValidOn (Gen.genF initR (QHNetRecR.preF ++ QHNetRecR.copyoND ++ leafMix ++ gateMix)).1 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
