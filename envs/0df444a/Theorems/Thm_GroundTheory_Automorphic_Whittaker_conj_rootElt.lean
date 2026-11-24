-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_conj_rootElt
-- name    : GroundTheory.Automorphic.Whittaker.conj_rootElt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:00.079317+00:00
-- url     : https://prove2.me/theorems/98255ae0-5862-4d69-9d97-2987fb31aa86
-- title:
--   Whittaker: conj root Elt
-- statement:
--   The Whittaker construction uses the conj root Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L434-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L434-L449

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

theorem GroundTheory.Automorphic.Whittaker.conj_rootElt (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n) (a : F) :
    (Iwasawa.diagGL F n t * permGL F w) * rootElt i j a * (Iwasawa.diagGL F n t * permGL F w)⁻¹ =
      rootElt (w i) (w j) ((t (w i) : F) / (t (w j) : F) * a) := by sorry
