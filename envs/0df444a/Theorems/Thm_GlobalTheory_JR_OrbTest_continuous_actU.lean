-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbTest_continuous_actU
-- name    : GlobalTheory.JR.OrbTest.continuous_actU
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:36.971915+00:00
-- url     : https://prove2.me/theorems/84992dce-45f6-4c85-83e0-9d446190e60b
-- title:
--   Orb Test: continuous act U
-- statement:
--   The Orb Test construction uses the continuous act U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitalIntegrandIsLocallyConstantCo.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitalIntegrandIsLocallyConstantCo.lean#L54-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProperStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCo
import Theorems.Thm_GlobalTheory_JR_OrbProper_continuous_actU

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

theorem GlobalTheory.JR.OrbTest.continuous_actU {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [ContinuousStar E] (X : Hn r F E) :
    Continuous (fun g : Matrix.unitaryGroup (Fin r) E => actU g X) := by sorry
