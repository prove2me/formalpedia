-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TensorLatticeUnitPart_extBil_tmul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart.extBil_tmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:43.786301+00:00
-- url     : https://prove2.me/theorems/da8ddeff-fb17-4c47-88dd-54320dd72327
-- title:
--   Tensor Lattice Unit Part: ext Bil tmul
-- statement:
--   The Tensor Lattice Unit Part construction uses the ext Bil tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/TensorLatticeUnitPart.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/TensorLatticeUnitPart.lean#L20-L22

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart.extBil_tmul (b : M →ₗ[O] M' →ₗ[O] M'') (r r' : R) (x : M) (y : M') :
    extBil R b (r ⊗ₜ[O] x) (r' ⊗ₜ[O] y) = (r * r') ⊗ₜ[O] b x y := by sorry
