-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_ht_law
-- name    : GlobalTheory.CompanionTheory.Plucker.ht_law
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:00.552981+00:00
-- url     : https://prove2.me/theorems/a9001f08-9d19-4b5f-9280-04b6ebe246fe
-- title:
--   Plucker: ht law
-- statement:
--   The Plucker construction uses the ht law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L269-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L269-L277

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]

theorem GlobalTheory.CompanionTheory.Plucker.ht_law (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (ι : Type) [Fintype ι] [DecidableEq ι] (s : Set ι) :
    IsHt (A.ratGL ι) (A.kGL ι) (stab R s) (A.htGL s) ∧
      ∀ p ∈ stab R s, ∀ k ∈ A.kGL ι, A.htGL s (p * k) = A.lg (bdet s p) := by sorry
