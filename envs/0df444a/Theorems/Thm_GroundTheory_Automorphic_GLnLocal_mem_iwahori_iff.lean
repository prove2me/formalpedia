-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_iwahori_iff
-- name    : GroundTheory.Automorphic.GLnLocal.mem_iwahori_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:39.460568+00:00
-- url     : https://prove2.me/theorems/f3c501c1-1ef8-4681-b741-fa7209837f8f
-- title:
--   GLn Local: mem iwahori iff
-- statement:
--   The GLn Local construction uses the mem iwahori iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L73-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L73-L85

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

theorem GroundTheory.Automorphic.GLnLocal.mem_iwahori_iff {g : GL (Fin n) F} :
    g ∈ iwahori F n ↔ (∀ i j, valuation F (g i j) ≤ 1) ∧
      (∀ i j, j < i → valuation F (g i j) < 1) ∧ ∀ i, valuation F (g i i) = 1 := by sorry
