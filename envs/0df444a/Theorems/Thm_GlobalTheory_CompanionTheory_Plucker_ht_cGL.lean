-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_ht_cGL
-- name    : GlobalTheory.CompanionTheory.Plucker.ht_cGL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:13.868784+00:00
-- url     : https://prove2.me/theorems/7a789b28-9aec-4e10-9fe5-77f046b481a0
-- title:
--   Plucker: ht c GL
-- statement:
--   The Plucker construction uses the ht c GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L279-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L279-L282

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

theorem GlobalTheory.CompanionTheory.Plucker.ht_cGL (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (t₀ : Sub ι m) (g : GL ι R) :
    A.htGL ({t₀} : Set (Sub ι m)) (cGL m g) = A.htGL (t₀.1 : Set ι) g := by sorry
