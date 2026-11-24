-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLHaarAdd_eq_addHaar
-- name    : GlobalTheory.CompanionTheory.QLHaarAdd.eq_addHaar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:40.429892+00:00
-- url     : https://prove2.me/theorems/ce5f74a6-2397-42ad-86b6-0b9067ead2fe
-- title:
--   QLHaar Add: eq add Haar
-- statement:
--   The QLHaar Add construction uses the eq add Haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixAdditiveHaarNormalized.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixAdditiveHaarNormalized.lean#L23-L36

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalized
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLHaarAdd

theorem GlobalTheory.CompanionTheory.QLHaarAdd.eq_addHaar {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (K₀ : TopologicalSpace.PositiveCompacts G) (hKo : IsOpen (K₀ : Set G)) (h0 : (0 : G) ∈ (K₀ : Set G))
    (dx : Measure G) [dx.IsAddLeftInvariant] (h1 : dx (K₀ : Set G) = 1) :
    dx = Measure.addHaarMeasure K₀ := by sorry
