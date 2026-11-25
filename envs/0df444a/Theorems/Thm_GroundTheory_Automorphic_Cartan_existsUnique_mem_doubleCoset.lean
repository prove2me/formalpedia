-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Cartan_existsUnique_mem_doubleCoset
-- name    : GroundTheory.Automorphic.Cartan.existsUnique_mem_doubleCoset
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:03.257891+00:00
-- url     : https://prove2.me/theorems/8354c509-34fb-5a8f-be93-832a2f0729ba
-- title:
--   Cartan: exists Unique mem double Coset
-- statement:
--   The Cartan construction uses the exists Unique mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Cartan.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Cartan.lean#L296-L301

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

theorem GroundTheory.Automorphic.Cartan.existsUnique_mem_doubleCoset (g : GL (Fin n) F) :
    ∃! μ : Fin n → ℤ, IsDominant μ ∧
      g ∈ doubleCoset (diagPow F n μ) (integralGL F n : Set (GL (Fin n) F)) (integralGL F n) := by sorry
