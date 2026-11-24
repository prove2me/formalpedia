-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_permAct_symm_apply
-- name    : GroundTheory.Automorphic.GLnLocal.permAct_symm_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:30:47.469033+00:00
-- url     : https://prove2.me/theorems/21530bfd-2c74-4cd8-a66d-fa276545e5ca
-- title:
--   GLn Local: perm Act symm apply
-- statement:
--   The GLn Local construction uses the perm Act symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L176-L178

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

theorem GroundTheory.Automorphic.GLnLocal.permAct_symm_apply (σ : Equiv.Perm (Fin n)) (a : Fin n → Multiplicative ℤ) (i : Fin n) :
    (permAct n σ).symm a i = a (σ i) := by sorry
