-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_exists_witness
-- name    : GlobalTheory.CompanionTheory.SmoothSpread.exists_witness
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:28.233965+00:00
-- url     : https://prove2.me/theorems/1b08baad-d94e-4916-abfa-6ff3ce24be87
-- title:
--   Smooth Spread: exists witness
-- statement:
--   The Smooth Spread construction uses the exists witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L16-L39

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

theorem GlobalTheory.CompanionTheory.SmoothSpread.exists_witness [Algebra.FormallySmooth T S] (Q : Algebra.Presentation T S ι σ) :
    ∃ h : ι → Q.Ring, (∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation)) ∧
      ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2 := by sorry
