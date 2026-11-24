-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_single_mul_diag_mul_permGL
-- name    : GroundTheory.Automorphic.Whittaker.single_mul_diag_mul_permGL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:57.067862+00:00
-- url     : https://prove2.me/theorems/6363f37a-5443-41a3-b1e1-e7e7c400433c
-- title:
--   Whittaker: single mul diag mul perm GL
-- statement:
--   The Whittaker construction uses the single mul diag mul perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L419-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L419-L432

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

theorem GroundTheory.Automorphic.Whittaker.single_mul_diag_mul_permGL (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (k j : Fin n)
    (b : F) :
    Matrix.single k (w j) b *
        ((Iwasawa.diagGL F n t * permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.single k j (b * (t (w j) : F)) := by sorry
