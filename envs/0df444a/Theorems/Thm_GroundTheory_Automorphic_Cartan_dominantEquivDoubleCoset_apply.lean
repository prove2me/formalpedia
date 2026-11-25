-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
-- name    : GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:39.442853+00:00
-- url     : https://prove2.me/theorems/a6ac3db2-7300-4da6-b12c-be4c29140059
-- title:
--   Cartan: dominant Equiv Double Coset apply
-- statement:
--   The Cartan construction uses the dominant Equiv Double Coset apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Cartan.lean#L320-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Cartan.lean#L320-L323

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulLeftCancelOfDetNeZero
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix
open GroundTheory.Automorphic.Cartan
open ValuativeRel GLnLocal DoubleCoset
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

theorem GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply (μ : {μ : Fin n → ℤ // IsDominant μ}) :
    dominantEquivDoubleCoset F n μ =
      DoubleCoset.mk (integralGL F n) (integralGL F n) (diagPow F n μ) := by sorry

attribute [defeq] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
