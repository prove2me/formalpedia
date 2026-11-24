-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_psiN_rootElt
-- name    : GroundTheory.Automorphic.Whittaker.psiN_rootElt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:17:26.106503+00:00
-- url     : https://prove2.me/theorems/a2af0065-00e9-471f-b922-5d4077dc01ea
-- title:
--   Whittaker: psi N root Elt
-- statement:
--   The Whittaker construction uses the psi N root Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L398-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L398-L403

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

theorem GroundTheory.Automorphic.Whittaker.psiN_rootElt (ψ₀ : AddChar F ℂ) {i j : Fin n} (h : i ≠ j) (a : F) :
    psiN ψ₀ (rootElt i j a) = if j.val = i.val + 1 then ψ₀ a else 1 := by sorry
