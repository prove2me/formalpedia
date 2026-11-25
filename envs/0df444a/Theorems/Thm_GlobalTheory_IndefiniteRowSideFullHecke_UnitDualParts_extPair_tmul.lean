-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitDualParts_extPair_tmul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.extPair_tmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:12.007007+00:00
-- url     : https://prove2.me/theorems/35161485-2632-4d51-be96-fcae36461221
-- title:
--   Unit Dual Parts: ext Pair tmul
-- statement:
--   The Unit Dual Parts construction uses the ext Pair tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnitDualParts.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnitDualParts.lean#L28-L32

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.extPair_tmul {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (β : M →ₗ[O] M' →ₗ[O] O) (r r' : R) (a : M) (a' : M') :
    extPair R β (r ⊗ₜ[O] a) (r' ⊗ₜ[O] a') = β a a' • (r * r') := by sorry
