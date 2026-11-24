-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_eq_mul_affineWeylGL_of_rowsReducedOn
-- name    : GroundTheory.Automorphic.GLnLocal.exists_eq_mul_affineWeylGL_of_rowsReducedOn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:58.854196+00:00
-- url     : https://prove2.me/theorems/30c1ddb8-8acb-4e3a-9994-ccea28419e02
-- title:
--   GLn Local: exists eq mul affine Weyl GL of rows Reduced On
-- statement:
--   The GLn Local construction uses the exists eq mul affine Weyl GL of rows Reduced On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L542-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L542-L582

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

theorem GroundTheory.Automorphic.GLnLocal.exists_eq_mul_affineWeylGL_of_rowsReducedOn (g : GL (Fin n) F)
    (hred : RowsReducedOn (g : Matrix (Fin n) (Fin n) F) Finset.univ) :
    ∃ w : ExtendedAffineWeyl n, ∃ t ∈ iwahori F n, g = t * affineWeylGL F n w := by sorry
