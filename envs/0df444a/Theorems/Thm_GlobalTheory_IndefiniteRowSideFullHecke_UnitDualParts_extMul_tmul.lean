-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitDualParts_extMul_tmul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.extMul_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:46.656795+00:00
-- url     : https://prove2.me/theorems/086cc55e-091c-4470-a4ae-29d5a5e9f222
-- title:
--   Unit Dual Parts: ext Mul tmul
-- statement:
--   The Unit Dual Parts construction uses the ext Mul tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnitDualParts.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnitDualParts.lean#L17-L21

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.extMul_tmul {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']
    (m : M ⊗[O] M' →ₗ[O] M'') (r r' : R) (a : M) (a' : M') :
    extMul R m (r ⊗ₜ[O] a) (r' ⊗ₜ[O] a') = (r * r') ⊗ₜ[O] m (a ⊗ₜ[O] a') := by sorry
