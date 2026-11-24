-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_rootElt
-- name    : GroundTheory.Automorphic.Whittaker.continuous_rootElt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:07.007043+00:00
-- url     : https://prove2.me/theorems/0ff0e74d-e7aa-415e-93e5-ed66cd3fd093
-- title:
--   Whittaker: continuous root Elt
-- statement:
--   The Whittaker construction uses the continuous root Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L490-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L490-L509

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ}
variable [IsTopologicalRing F]

theorem GroundTheory.Automorphic.Whittaker.continuous_rootElt (i j : Fin n) : Continuous (rootElt i j : F → GL (Fin n) F) := by sorry
