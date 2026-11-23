-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_nondeg
-- name    : GlobalTheory.JR.WeilQuad.FourierTest.beta_nondeg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:10.58096+00:00
-- url     : https://prove2.me/theorems/9902826d-0082-4c50-8742-0fdd7c103064
-- title:
--   Fourier Test: beta nondeg
-- statement:
--   The Fourier Test construction uses the beta nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierPreservesTestAdditive.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierPreservesTestAdditive.lean#L91-L93

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

theorem GlobalTheory.JR.WeilQuad.FourierTest.beta_nondeg [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).Nondegenerate := by sorry
