-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SubEig_smooth_sub
-- name    : GlobalTheory.CompanionTheory.SubEig.smooth_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:14:40.638651+00:00
-- url     : https://prove2.me/theorems/19bc2f9c-27ae-4f4f-b60b-da735f606cde
-- title:
--   Sub Eig: smooth sub
-- statement:
--   The Sub Eig construction uses the smooth sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SubquotientOfEigencharacter.lean#L138-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SubquotientOfEigencharacter.lean#L138-L145

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothQuot
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisLast
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SubquotientOfEigencharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubEig
variable {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.CompanionTheory.SubEig.smooth_sub {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by sorry
