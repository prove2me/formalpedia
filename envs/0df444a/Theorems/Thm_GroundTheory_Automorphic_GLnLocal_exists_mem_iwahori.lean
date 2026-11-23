-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_mem_iwahori
-- name    : GroundTheory.Automorphic.GLnLocal.exists_mem_iwahori
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:10.060149+00:00
-- url     : https://prove2.me/theorems/400ec9d2-361e-42fe-aed5-04a26fb72530
-- title:
--   GLn Local: exists mem iwahori
-- statement:
--   The GLn Local construction uses the exists mem iwahori property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L44-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L44-L71

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

theorem GroundTheory.Automorphic.GLnLocal.exists_mem_iwahori (M : Matrix (Fin n) (Fin n) F)
    (h1 : ∀ i j, valuation F (M i j) ≤ 1) (h2 : ∀ i j, j < i → valuation F (M i j) < 1)
    (h3 : ∀ i, valuation F (M i i) = 1) :
    ∃ x ∈ iwahori F n, (x : Matrix (Fin n) (Fin n) F) = M := by sorry
