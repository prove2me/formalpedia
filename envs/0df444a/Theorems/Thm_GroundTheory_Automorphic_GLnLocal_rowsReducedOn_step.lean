-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_rowsReducedOn_step
-- name    : GroundTheory.Automorphic.GLnLocal.rowsReducedOn_step
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:30:35.450646+00:00
-- url     : https://prove2.me/theorems/e4bc553d-e6a8-4449-984d-0ca12aeb2161
-- title:
--   GLn Local: rows Reduced On step
-- statement:
--   The GLn Local construction uses the rows Reduced On step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L300-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L300-L494

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

theorem GroundTheory.Automorphic.GLnLocal.rowsReducedOn_step (h : GL (Fin n) F) (R : Finset (Fin n)) (hR : R ≠ Finset.univ)
    (hred : RowsReducedOn (h : Matrix (Fin n) (Fin n) F) R) :
    ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n, ∃ r ∉ R,
      RowsReducedOn ((x * h * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (insert r R) := by sorry
