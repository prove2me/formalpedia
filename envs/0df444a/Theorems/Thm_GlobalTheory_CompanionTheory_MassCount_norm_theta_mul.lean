-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MassCount_norm_theta_mul
-- name    : GlobalTheory.CompanionTheory.MassCount.norm_theta_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:14.449081+00:00
-- url     : https://prove2.me/theorems/8795ef55-a660-479e-8f7b-e4479033b6dd
-- title:
--   Mass Count: norm theta mul
-- statement:
--   The Mass Count construction uses the norm theta mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormThetaMul.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormThetaMul.lean#L22-L35

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GaloisBoundSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormThetaMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MassCount
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.MassCount.norm_theta_mul [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (ε : ℝ) (x : F) (w : InfinitePlace F) :
    ‖(θ ε * algebraMap F (InfiniteAdeleRing F) x) w‖ = |ε| * w x := by sorry
