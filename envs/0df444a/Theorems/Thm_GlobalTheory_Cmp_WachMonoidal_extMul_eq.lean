-- Prove2me | Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_extMul_eq
-- name    : GlobalTheory.Cmp.WachMonoidal.extMul_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:26:35.987804+00:00
-- url     : https://prove2.me/theorems/573a832c-3ced-404e-a1d8-189b7bc02bcb
-- title:
--   Wach Monoidal: ext Mul eq
-- statement:
--   The Wach Monoidal construction uses the ext Mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitSumTensorDualOfWachMonoidal.lean#L21-L34

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

theorem GlobalTheory.Cmp.WachMonoidal.extMul_eq (b : M →ₗ[O] M' →ₗ[O] M'') (u : R ⊗[O] M) (w : R ⊗[O] M') :
    UnitDualParts.extMul R (TensorProduct.lift b) u w = TensorLatticeUnitPart.extBil R b u w := by sorry
