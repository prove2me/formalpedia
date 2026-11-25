-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_diag_mul_permGL_eq
-- name    : GroundTheory.Automorphic.Whittaker.sigma_diag_mul_permGL_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:02.846653+00:00
-- url     : https://prove2.me/theorems/b4557609-5d11-42cb-aae3-b2eebc21d630
-- title:
--   Whittaker: sigma diag mul perm GL eq
-- statement:
--   The Whittaker construction uses the sigma diag mul perm GL eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L295-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L295-L311

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

theorem GroundTheory.Automorphic.Whittaker.sigma_diag_mul_permGL_eq (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n))
    (hw : ∀ b, w (Fin.rev (w b)) = Fin.rev b) (ht : ∀ b, t (w b) = t (Fin.rev b)) :
    sigma (Iwasawa.diagGL F n t * permGL F w) = Iwasawa.diagGL F n t * permGL F w := by sorry
