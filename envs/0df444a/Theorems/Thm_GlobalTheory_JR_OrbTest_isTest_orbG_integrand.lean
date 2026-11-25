-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbTest_isTest_orbG_integrand
-- name    : GlobalTheory.JR.OrbTest.isTest_orbG_integrand
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:52.170045+00:00
-- url     : https://prove2.me/theorems/23916dbb-1d8f-4fdb-b70e-a37ae20f63fd
-- title:
--   Orb Test: is Test orb G integrand
-- statement:
--   The Orb Test construction uses the is Test orb G integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitalIntegrandIsLocallyConstantCo.lean#L66-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitalIntegrandIsLocallyConstantCo.lean#L66-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProperStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbTest

theorem GlobalTheory.JR.OrbTest.isTest_orbG_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f' : Gl r F → ℂ) (hf : IsTest f') (Y : Gl r F)
    (hY : Delta (inv Y) ≠ 0) :
    IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y)) := by sorry
