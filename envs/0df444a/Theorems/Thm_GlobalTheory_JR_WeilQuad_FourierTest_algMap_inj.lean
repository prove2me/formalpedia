-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_algMap_inj
-- name    : GlobalTheory.JR.WeilQuad.FourierTest.algMap_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:13.497978+00:00
-- url     : https://prove2.me/theorems/4639820c-025b-43e3-931d-90b05795d2a5
-- title:
--   Fourier Test: alg Map inj
-- statement:
--   The Fourier Test construction uses the alg Map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierPreservesTestAdditive.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierPreservesTestAdditive.lean#L34-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.FourierTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.WeilQuad.FourierTest.algMap_inj (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    Function.Injective (algebraMap A.K A.L) := by sorry
