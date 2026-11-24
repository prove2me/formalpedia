-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_ext_gl
-- name    : GlobalTheory.CompanionTheory.RgEisPar.ext_gl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:49.327568+00:00
-- url     : https://prove2.me/theorems/47203925-2ea1-4647-927a-34dd6f0b7ae8
-- title:
--   Rg Eis Par: ext gl
-- statement:
--   The Rg Eis Par construction uses the ext gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLawOfBlockDet.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLawOfBlockDet.lean#L45-L56

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisPar
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

theorem GlobalTheory.CompanionTheory.RgEisPar.ext_gl (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (κ : Type) [Fintype κ] [DecidableEq κ]
    (t : Set κ) : IsHt (A.ratGL κ) (A.kGL κ) (stab R t) (A.htGL t) ∧
      ∀ p ∈ stab R t, ∀ k ∈ A.kGL κ, A.htGL t (p * k) = A.lg (bdet t p) := by sorry
