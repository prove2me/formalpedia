-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_tensorToProd_injective
-- name    : GlobalTheory.LocFlat.CFac.tensorToProd_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:12:49.935563+00:00
-- url     : https://prove2.me/theorems/7f1afb86-6ceb-4d3c-ab75-13d943c041fd
-- title:
--   CFac: tensor To Prod injective
-- statement:
--   The CFac construction uses the tensor To Prod injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLinearOfBilinearSchwartzBruhatProduct.lean#L24-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLinearOfBilinearSchwartzBruhatProduct.lean#L24-L49

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

theorem GlobalTheory.LocFlat.CFac.tensorToProd_injective (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Function.Injective (tensorToProd X Y) := by sorry
