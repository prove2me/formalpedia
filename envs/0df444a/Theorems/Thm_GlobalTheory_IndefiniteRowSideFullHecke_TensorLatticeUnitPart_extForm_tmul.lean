-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TensorLatticeUnitPart_extForm_tmul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart.extForm_tmul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:31.063804+00:00
-- url     : https://prove2.me/theorems/b8f2e3b9-98f7-58af-bf37-33336566772c
-- title:
--   Tensor Lattice Unit Part: ext Form tmul
-- statement:
--   The Tensor Lattice Unit Part construction uses the ext Form tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/TensorLatticeUnitPart.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/TensorLatticeUnitPart.lean#L27-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

theorem GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart.extForm_tmul (b : M →ₗ[O] M' →ₗ[O] O) (r r' : R) (x : M) (y : M') :
    extForm R b (r ⊗ₜ[O] x) (r' ⊗ₜ[O] y) = b x y • (r * r') := by sorry
