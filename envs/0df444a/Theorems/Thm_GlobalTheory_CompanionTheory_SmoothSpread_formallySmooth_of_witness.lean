-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_formallySmooth_of_witness
-- name    : GlobalTheory.CompanionTheory.SmoothSpread.formallySmooth_of_witness
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:34.944434+00:00
-- url     : https://prove2.me/theorems/f8cbf36a-236a-41c3-a29f-0ca22e72b11b
-- title:
--   Smooth Spread: formally Smooth of witness
-- statement:
--   The Smooth Spread construction uses the formally Smooth of witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L41-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L41-L84

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothSpread
variable {T S ι σ : Type} [CommRing T] [CommRing S] [Algebra T S]

theorem GlobalTheory.CompanionTheory.SmoothSpread.formallySmooth_of_witness (Q : Algebra.Presentation T S ι σ) (h : ι → Q.Ring)
    (h1 : ∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation))
    (h2 : ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2) :
    Algebra.FormallySmooth T S := by sorry
