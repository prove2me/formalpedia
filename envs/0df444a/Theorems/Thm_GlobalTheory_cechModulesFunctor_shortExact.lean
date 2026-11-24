-- Prove2me | Theorems.Thm_GlobalTheory_cechModulesFunctor_shortExact
-- name    : GlobalTheory.cechModulesFunctor_shortExact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:20:25.880998+00:00
-- url     : https://prove2.me/theorems/b98a0795-a55e-4cfb-b20c-f2ccc0578b22
-- title:
--   Global Theory: cech Modules Functor short Exact
-- statement:
--   The Global Theory construction uses the cech Modules Functor short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L225-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L225-L232

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

theorem GlobalTheory.cechModulesFunctor_shortExact (S : ShortComplex X.Modules)
    (h : ∀ s : Finset ι, s.Nonempty →
      Function.Injective (S.f.app (cechOpen V U s)) ∧
      Function.Exact (S.f.app (cechOpen V U s)) (S.g.app (cechOpen V U s)) ∧
      Function.Surjective (S.g.app (cechOpen V U s))) :
    (S.map (cechModulesFunctor R V U)).ShortExact := by sorry
