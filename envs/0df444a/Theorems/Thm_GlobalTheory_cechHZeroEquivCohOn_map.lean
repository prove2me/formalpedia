-- Prove2me | Theorems.Thm_GlobalTheory_cechHZeroEquivCohOn_map
-- name    : GlobalTheory.cechHZeroEquivCohOn_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:59.448804+00:00
-- url     : https://prove2.me/theorems/c3919200-f426-586f-b7eb-f510844373df
-- title:
--   Global Theory: cech HZero Equiv Coh On map
-- statement:
--   The Global Theory construction uses the cech HZero Equiv Coh On map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L332-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L332-L337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)
variable [LinearOrder ι]
variable {V U} (hc : V ≤ ⨆ i, U i)
variable {F}

theorem GlobalTheory.cechHZeroEquivCohOn_map (φ : F ⟶ G) (x : cechH R F V U 0) :
    cechHZeroEquivCohOn R G hc ((cechHMap R V U φ 0).hom x) =
      cohOn.map R φ V 0 (cechHZeroEquivCohOn R F hc x) := by sorry
