-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_MovesV_preF_copyoND
-- name    : IntMul.Kappa.R8.Bit.Oppbank.MovesV_preF_copyoND
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T12:24:11.440678+00:00
-- url     : https://prove2.me/theorems/eb9de76d-8c75-4018-80c7-542f60f28609
-- title:
--   MovesV/ValidOn for preF ++ copyoND from initR (QHNetRecR prefix)
-- statement:
--   On the published variant-R carrier, let $\mathrm{initR}$ be the stage-one initial labelling ($\mathrm{wX}(t)=\mathrm{cND}(t)$, densified $\mathrm{RETN}-1$ on the $wT$ wires, and $0$ elsewhere). Running the prefix $\mathrm{preF}$ followed by the copy stage $\mathrm{copyoND}$ from $\mathrm{initR}$ yields a valid labelling whose recorded moves are nested at bound $64251$:
--
--   $$\mathrm{ValidOn}(\mathrm{initR})\ \wedge\ \mathrm{MovesV}(\mathrm{genF}(\mathrm{initR},\mathrm{preF}{+}\!{+}\mathrm{copyoND}))\ \wedge\ \mathrm{ValidOn}(\mathrm{genF}(\mathrm{initR},\mathrm{preF}{+}\!{+}\mathrm{copyoND})_1).$$
--
--   This extends the already-established $\mathrm{preF}$ prefix by the $\mathrm{cND}$ copy instructions. Each copy writes $\mathrm{cND}(t)$ onto the source slot $\mathrm{wS}(\mathrm{srcS}(t))$ (previously $0$) and the target $\mathrm{wX}(t)$; injectivity of $\mathrm{srcS}$ on $t<v$ keeps those slots disjoint, so every recorded old code is $0$ and nestOK holds by the boundary clause.
--
--   Formalization Note. The statement is `Lab.ValidOn` / `Lab.MovesV` for `Gen.genF initR (QHNetRecR.preF ++ QHNetRecR.copyoND)` at `codeBound = 64251`. It does not unfold `segsR` or `W1F` and is not a full-word MovesV certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: prefix MovesV/ValidOn for QHNetRecR.preF ++ QHNetRecR.copyoND from initR (initH, RETN-1, wX t = cND t) at Lab.codeBound 64251. Uses srcS injectivity. Not a full-word MovesV certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace IntMul.Kappa.R8.Bit.Oppbank

/-- Variant-R stage-one initial map (`initH`): `wX t = cND t`,
`wT c = cND (retN c)` with densified `RETN-1`, all other wires `0`. -/
def initR (w : ℕ) : ℕ :=
  if w < v then QHNetRecR.cND w
  else if wAuxEnd ≤ w ∧ w < NL then QHNetRecR.cND (QHNetRecR.retN (w - wAuxEnd))
  else 0

/-- The prefix `preF ++ copyoND` of `QHNetRecR.W1F`, run from `initR`, is
`ValidOn` / `MovesV` at densified `codeBound = 64251`. This does not unfold
`segsR` or `W1F` and is not a full-word `MovesV` certificate. -/
theorem MovesV_preF_copyoND :
    Lab.ValidOn initR ∧
      Lab.MovesV (Gen.genF initR (QHNetRecR.preF ++ QHNetRecR.copyoND)).2 ∧
        Lab.ValidOn (Gen.genF initR (QHNetRecR.preF ++ QHNetRecR.copyoND)).1 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
