-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarUnimod_isMulRightInvariant_of_isUnimod
-- name    : GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:33.655802+00:00
-- url     : https://prove2.me/theorems/3487e18e-e14a-4e65-9120-92a4aeb72ffe
-- title:
--   Haar Unimod: is Mul Right Invariant of is Unimod
-- statement:
--   The Haar Unimod construction uses the is Mul Right Invariant of is Unimod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHaarRightInvariant.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHaarRightInvariant.lean#L11-L18

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarUnimod
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

theorem GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G →
      ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by sorry
