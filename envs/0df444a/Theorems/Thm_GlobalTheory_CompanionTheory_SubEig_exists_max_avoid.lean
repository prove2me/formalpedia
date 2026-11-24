-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SubEig_exists_max_avoid
-- name    : GlobalTheory.CompanionTheory.SubEig.exists_max_avoid
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:15:22.935009+00:00
-- url     : https://prove2.me/theorems/757364dd-3ef8-456a-9dc4-00bd5b7089f8
-- title:
--   Sub Eig: exists max avoid
-- statement:
--   The Sub Eig construction uses the exists max avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SubquotientOfEigencharacter.lean#L30-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SubquotientOfEigencharacter.lean#L30-L64

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

theorem GlobalTheory.CompanionTheory.SubEig.exists_max_avoid (ρ : Representation ℂ G U) {u : U} (hu : u ≠ 0) :
    ∃ T : Subrepresentation ρ, u ∉ T.toSubmodule ∧
      ∀ T' : Subrepresentation ρ, T ≤ T' → u ∉ T'.toSubmodule → T' = T := by sorry
