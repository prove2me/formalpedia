-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_measure_quad
-- name    : GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:27.550876+00:00
-- url     : https://prove2.me/theorems/d366dccb-b579-482e-bfd8-5d9fbb1aed68
-- title:
--   Quad Iso: measure quad
-- statement:
--   The Quad Iso construction uses the measure quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L192-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean#L192-L222

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
variable [MeasurableSpace K] [BorelSpace K]

theorem GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad [SecondCountableTopology K] [IsTopologicalRing K] (lam : Measure K) [lam.IsAddLeftInvariant]
    (hfin : lam {s | Valued.v s < 1} ≠ ⊤) {a c : K}
    (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1) {A : Set K} (hA : MeasurableSet A) :
    lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by sorry
