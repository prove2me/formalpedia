-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SubEig_smooth_quot
-- name    : GlobalTheory.CompanionTheory.SubEig.smooth_quot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:15:57.879924+00:00
-- url     : https://prove2.me/theorems/7b901ca7-6994-4d21-b8cb-d67c514f0a47
-- title:
--   Sub Eig: smooth quot
-- statement:
--   The Sub Eig construction uses the smooth quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SubquotientOfEigencharacter.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SubquotientOfEigencharacter.lean#L147-L149

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothQuot
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisLast
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SubquotientOfEigencharacter
import Theorems.Thm_UpperTheory_Reformulated_B_Gwb5_smooth_quot

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

theorem GlobalTheory.CompanionTheory.SubEig.smooth_quot {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (T : Submodule ℂ U)
    (hst : ∀ g, T ≤ T.comap (ρ g)) : IsSmooth (ρ.quotient T hst) := by sorry
