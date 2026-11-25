-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_exists_valBall_of_isCompact
-- name    : GroundTheory.Automorphic.GodementJacquet.exists_valBall_of_isCompact
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:10.862992+00:00
-- url     : https://prove2.me/theorems/a77172b9-d199-46a6-b2c3-f00c1b0318d0
-- title:
--   Godement Jacquet: exists val Ball of is Compact
-- statement:
--   The Godement Jacquet construction uses the exists val Ball of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean#L90-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJZetaDefs.lean#L90-L113

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
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
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.GodementJacquet.exists_valBall_of_isCompact {K : Set (Matrix (Fin n) (Fin n) F)} (hK : IsCompact K) :
    ∃ A : ℕ, ∀ X ∈ K, ∀ i j, X i j ∈ LocalField.valBall F (-(A : ℤ)) := by sorry
