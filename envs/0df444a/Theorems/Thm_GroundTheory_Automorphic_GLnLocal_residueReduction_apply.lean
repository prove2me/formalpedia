-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_residueReduction_apply
-- name    : GroundTheory.Automorphic.GLnLocal.residueReduction_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:10.744751+00:00
-- url     : https://prove2.me/theorems/6cf17c5d-b65a-4815-8b6a-8e0a944ab5c0
-- title:
--   GLn Local: residue Reduction apply
-- statement:
--   The GLn Local construction uses the residue Reduction apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L24-L27

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

theorem GroundTheory.Automorphic.GLnLocal.residueReduction_apply (u : GL (Fin n) 𝒪[F]) (i j : Fin n) :
    (residueReduction F n u : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField 𝒪[F])) i j =
      IsLocalRing.residue 𝒪[F] (u i j) := by sorry
