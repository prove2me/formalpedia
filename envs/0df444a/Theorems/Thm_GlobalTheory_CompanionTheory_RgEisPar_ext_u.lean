-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_ext_u
-- name    : GlobalTheory.CompanionTheory.RgEisPar.ext_u
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:21.403034+00:00
-- url     : https://prove2.me/theorems/da379f96-d82e-40de-8208-0b4094d19b06
-- title:
--   Rg Eis Par: ext u
-- statement:
--   The Rg Eis Par construction uses the ext u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLawOfBlockDet.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLawOfBlockDet.lean#L62-L77

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

theorem GlobalTheory.CompanionTheory.RgEisPar.ext_u (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (t : Set κ) (hI : Iwa (A.uQ ε t) (A.uK ε κ)) :
    IsHt (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (A.uH ε t) ∧
      ∀ p ∈ A.uQ ε t, ∀ k ∈ A.uK ε κ, A.uH ε t (p * k) = A.lg (bdet (Sum.inl '' t) p.1) := by sorry
