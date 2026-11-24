-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLHaarAdd_finite_on_compacts
-- name    : GlobalTheory.CompanionTheory.QLHaarAdd.finite_on_compacts
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:55.274545+00:00
-- url     : https://prove2.me/theorems/9164155a-e44e-4d63-a0a2-fb997d5b8bf6
-- title:
--   QLHaar Add: finite on compacts
-- statement:
--   The QLHaar Add construction uses the finite on compacts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixAdditiveHaarNormalized.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixAdditiveHaarNormalized.lean#L8-L21

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

theorem GlobalTheory.CompanionTheory.QLHaarAdd.finite_on_compacts {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] {K : Set G} (hKo : IsOpen K) (h0 : (0 : G) ∈ K)
    (dx : Measure G) [dx.IsAddLeftInvariant] (h1 : dx K = 1) : IsFiniteMeasureOnCompacts dx := by sorry
