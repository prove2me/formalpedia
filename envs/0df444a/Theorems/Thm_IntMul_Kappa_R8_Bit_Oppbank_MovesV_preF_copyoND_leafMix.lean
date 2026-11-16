-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_MovesV_preF_copyoND_leafMix
-- name    : IntMul.Kappa.R8.Bit.Oppbank.MovesV_preF_copyoND_leafMix
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T13:29:51.513798+00:00
-- url     : https://prove2.me/theorems/8ce5876f-1325-4de6-b0d4-b8ec104c2498
-- title:
--   MovesV/ValidOn for preF ++ copyoND ++ leafMix from initR (QHNetRecR leaf prefix)
-- statement:
--   # Leaf prefix of the variant-R word is a valid nested move
--
--   On the published variant-R carrier, let $\mathrm{initR}$ be the stage-one initial labelling ($\mathrm{wX}(t)=\mathrm{cND}(t)$, densified $\mathrm{RETN}-1$ on the $wT$ wires, and $0$ elsewhere). Let $\mathrm{leafMix}$ be the list of $v=1771$ leaf mix-forward records whose extra slots occupy the open interval between consecutive $\mathrm{srcS}$ values (and, for the last leaf, up to the leaf slot bound $11099$). Write $\mathrm{copyoND\_leafMix}$ for the concatenation of the copy stage $\mathrm{copyoND}$ with $\mathrm{leafMix}$. Running the prefix $\mathrm{preF}$ followed by $\mathrm{copyoND\_leafMix}$ from $\mathrm{initR}$ yields a valid labelling whose recorded moves are nested at bound $64251$:
--
--   $$\mathrm{ValidOn}(\mathrm{initR})\ \wedge\ \mathrm{MovesV}(\mathrm{genF}(\mathrm{initR},\mathrm{preF}{+}\!{+}\mathrm{copyoND\_leafMix}))\ \wedge\ \mathrm{ValidOn}(\mathrm{genF}(\mathrm{initR},\mathrm{preF}{+}\!{+}\mathrm{copyoND\_leafMix})_1).$$
--
--   This extends the already-established $\mathrm{preF}{+}\!{+}\mathrm{copyoND}$ prefix by the first $1771$ leaf records of the mix-forward schedule. After the copy stage, each pivot slot $\mathrm{wS}(\mathrm{srcS}(t))$ already carries $\mathrm{cND}(t)$, and each extra slot in a leaf interval is still $0$, so every recorded leaf move is a boundary write.
--
--   Formalization Note. The statement is `Lab.ValidOn` / `Lab.MovesV` for `Gen.genF initR (QHNetRecR.preF ++ copyoND_leafMix)` at `codeBound = 64251`, with `copyoND_leafMix := QHNetRecR.copyoND ++ leafMix`. It does not unfold `segsR` or `W1F`, does not cover the later mix-forward gates or preloads, and is not a full-word MovesV certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: prefix MovesV/ValidOn for QHNetRecR.preF ++ copyoND ++ leafMix from initR (initH, RETN-1, wX t = cND t) at Lab.codeBound 64251. leafMix is the 1771 leaf mix-forward records. Not a full-word MovesV certificate; does not unfold segsR or W1F.

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

/-- Exclusive upper bound on source-slot indices appearing in leaf extras. -/
def leafSlotBound : ℕ := 11099

/-- Exclusive end of the open slot interval belonging to leaf `t`. -/
def leafHi (t : ℕ) : ℕ := if t + 1 = v then leafSlotBound else QHNetRecR.srcS (t + 1)

/-- Extra source slots written by leaf `t`: strictly between consecutive `srcS`
values, or up to `leafSlotBound` for the last leaf. -/
def leafExtras (t : ℕ) : List ℕ :=
  List.range' (QHNetRecR.srcS t + 1) (leafHi t - (QHNetRecR.srcS t + 1))

/-- The mix-forward instruction for leaf `t`. -/
def leafAt (t : ℕ) : QHNetRecR.LInstr :=
  QHNetRecR.mk (QHNetRecR.cND t)
    (leafExtras t |>.map fun o => (wS o, wS (QHNetRecR.srcS t)))

/-- The 1771 leaf mix-forward records. Marked irreducible so the concrete
`List.range v` map is never unfolded. -/
@[irreducible] def leafMix : List QHNetRecR.LInstr := (List.range v).map leafAt

/-- Concatenation of the copy stage with the leaf mix-forward pack. -/
@[irreducible] def copyoND_leafMix : List QHNetRecR.LInstr :=
  QHNetRecR.copyoND ++ leafMix

/-- The prefix `preF ++ copyoND_leafMix` of `QHNetRecR.W1F`, run from `initR`,
is `ValidOn` / `MovesV` at densified `codeBound = 64251`. This does not unfold
`segsR` or `W1F`, does not cover later mix-forward gates or preloads, and is
not a full-word `MovesV` certificate. -/
theorem MovesV_preF_copyoND_leafMix :
    Lab.ValidOn initR ∧
      Lab.MovesV (Gen.genF initR (QHNetRecR.preF ++ copyoND_leafMix)).2 ∧
        Lab.ValidOn (Gen.genF initR (QHNetRecR.preF ++ copyoND_leafMix)).1 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
