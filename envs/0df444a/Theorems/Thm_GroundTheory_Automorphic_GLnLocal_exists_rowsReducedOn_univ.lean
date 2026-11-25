-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_rowsReducedOn_univ
-- name    : GroundTheory.Automorphic.GLnLocal.exists_rowsReducedOn_univ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:00.484663+00:00
-- url     : https://prove2.me/theorems/cf957563-6fc6-4fc7-bfa1-e490bac7979e
-- title:
--   GLn Local: exists rows Reduced On univ
-- statement:
--   The GLn Local construction uses the exists rows Reduced On univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L496-L520
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L496-L520

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

theorem GroundTheory.Automorphic.GLnLocal.exists_rowsReducedOn_univ (g : GL (Fin n) F) :
    ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n,
      RowsReducedOn ((x * g * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) Finset.univ := by sorry
