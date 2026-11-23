-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_rootElt_apply
-- name    : GroundTheory.Automorphic.Whittaker.rootElt_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:45.381274+00:00
-- url     : https://prove2.me/theorems/f5fa1c46-d0c0-4519-a089-577ebe91ca0e
-- title:
--   Whittaker: root Elt apply
-- statement:
--   The Whittaker construction uses the root Elt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L332-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L332-L335

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
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.rootElt_apply {i j : Fin n} (h : i ≠ j) (a : F) (r c : Fin n) :
    ((rootElt i j a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
      (1 : Matrix (Fin n) (Fin n) F) r c + if i = r ∧ j = c then a else 0 := by sorry
