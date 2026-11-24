-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_mem_kGL
-- name    : GlobalTheory.CompanionTheory.Plucker.mem_kGL
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:39.778853+00:00
-- url     : https://prove2.me/theorems/9e19f5fb-6c7b-4571-a874-affbf2bc4caa
-- title:
--   Plucker: mem k GL
-- statement:
--   The Plucker construction uses the mem k GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L227-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L227-L229

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
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]

theorem GlobalTheory.CompanionTheory.Plucker.mem_kGL (A : Ad E R) {k : GL ι R} : k ∈ A.kGL ι ↔
    (∀ r c, (k : Matrix ι ι R) r c ∈ A.O ∧ ((k⁻¹ : GL ι R) : Matrix ι ι R) r c ∈ A.O) ∧
    ∀ w, (k : Matrix ι ι R).map (A.φ w) ∈ Matrix.unitaryGroup ι ℂ := by sorry
