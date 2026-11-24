-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_valuation_le_of_mem_doubleCoset
-- name    : GroundTheory.Automorphic.GLnLocal.valuation_le_of_mem_doubleCoset
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:56.618366+00:00
-- url     : https://prove2.me/theorems/8bf42c6c-98d2-4e5a-a0ff-ef5c75465d0e
-- title:
--   GLn Local: valuation le of mem double Coset
-- statement:
--   The GLn Local construction uses the valuation le of mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L209-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L209-L251

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
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
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)

theorem GroundTheory.Automorphic.GLnLocal.valuation_le_of_mem_doubleCoset {w w' : ExtendedAffineWeyl n}
    (h : affineWeylGL F n w' ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n))
    (c : Fin n) :
    valuation F ϖ ^ (w'.left (w'.right c)).toAdd ≤ valuation F ϖ ^ (w.left (w.right c)).toAdd ∧
      (w.right c < w'.right c →
        valuation F ϖ ^ (w'.left (w'.right c)).toAdd <
          valuation F ϖ ^ (w.left (w.right c)).toAdd) := by sorry
