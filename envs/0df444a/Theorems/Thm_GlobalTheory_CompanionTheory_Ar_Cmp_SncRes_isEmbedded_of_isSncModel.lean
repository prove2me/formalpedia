-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_isEmbedded_of_isSncModel
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:13.664806+00:00
-- url     : https://prove2.me/theorems/90f90e0d-a922-5268-995d-312c534795a3
-- title:
--   Snc Res: is Embedded of is Snc Model
-- statement:
--   The Snc Res construction uses the is Embedded of is Snc Model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncModelEmbeddedLogResolution.lean#L162-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncModelEmbeddedLogResolution.lean#L162-L219

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterAlgRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbeddedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndConeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∃ R : AnLogRes (mCoordIdeal y) J e, IsEmbedded R.A (mCoordIdeal y) R.U R.lift := by sorry
