-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_tensorToProd_tmul
-- name    : GlobalTheory.LocFlat.CFac.tensorToProd_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:54.163872+00:00
-- url     : https://prove2.me/theorems/fcf6708a-0449-4036-a8fe-bce9840657c9
-- title:
--   CFac: tensor To Prod tmul
-- statement:
--   The CFac construction uses the tensor To Prod tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLinearOfBilinearSchwartzBruhatProduct.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLinearOfBilinearSchwartzBruhatProduct.lean#L20-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac

theorem GlobalTheory.LocFlat.CFac.tensorToProd_tmul {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) :
    tensorToProd X Y (f ⊗ₜ g) = prodSB f g := by sorry
