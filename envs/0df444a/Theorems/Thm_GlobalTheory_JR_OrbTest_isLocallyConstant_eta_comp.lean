-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbTest_isLocallyConstant_eta_comp
-- name    : GlobalTheory.JR.OrbTest.isLocallyConstant_eta_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:27.813545+00:00
-- url     : https://prove2.me/theorems/eba98ca1-0601-4d31-8d95-63a87bde2c58
-- title:
--   Orb Test: is Locally Constant eta comp
-- statement:
--   The Orb Test construction uses the is Locally Constant eta comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitalIntegrandIsLocallyConstantCo.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitalIntegrandIsLocallyConstantCo.lean#L19-L37

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

theorem GlobalTheory.JR.OrbTest.isLocallyConstant_eta_comp {X F : Type} [TopologicalSpace X] [NormedField F] [IsUltrametricDist F]
    (h : X → F) (hc : Continuous h) (h0 : ∀ x, h x ≠ 0) : IsLocallyConstant (fun x => eta (h x)) := by sorry
