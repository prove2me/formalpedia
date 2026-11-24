-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_stab_of_cGL
-- name    : GlobalTheory.CompanionTheory.Plucker.stab_of_cGL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:22.403793+00:00
-- url     : https://prove2.me/theorems/6ce57106-0060-4078-827f-6c98df8b3226
-- title:
--   Plucker: stab of c GL
-- statement:
--   The Plucker construction uses the stab of c GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L200-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L200-L220

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

theorem GlobalTheory.CompanionTheory.Plucker.stab_of_cGL (A : Ad E R) (hi : Function.Injective A.i) {t₀ : Sub ι m} {γ : GL ι R} (hγ : γ ∈ A.ratGL ι)
    (h : cGL m γ ∈ stab R ({t₀} : Set (Sub ι m))) : γ ∈ stab R (t₀.1 : Set ι) := by sorry
