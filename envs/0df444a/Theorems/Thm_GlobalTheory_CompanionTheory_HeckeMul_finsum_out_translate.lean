-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_finsum_out_translate
-- name    : GlobalTheory.CompanionTheory.HeckeMul.finsum_out_translate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:20.577733+00:00
-- url     : https://prove2.me/theorems/2202c0bd-dff9-4ca1-862c-f919cfc6eaee
-- title:
--   Hecke Mul: finsum out translate
-- statement:
--   The Hecke Mul construction uses the finsum out translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L21-L29

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.HeckeMul.finsum_out_translate {M : Type} [AddCommMonoid M] (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (a : G) :
    ∑ᶠ q : G ⧸ K, φ (a * q.out) = ∑ᶠ q : G ⧸ K, φ q.out := by sorry
