-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_eq_of_prod_bottomRows_eq
-- name    : GroundTheory.Automorphic.Whittaker.eq_of_prod_bottomRows_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:41:13.362933+00:00
-- url     : https://prove2.me/theorems/d2e2566d-1a35-4195-b534-d76c5fc5d0f5
-- title:
--   Whittaker: eq of prod bottom Rows eq
-- statement:
--   The Whittaker construction uses the eq of prod bottom Rows eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L524-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L524-L539

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
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

theorem GroundTheory.Automorphic.Whittaker.eq_of_prod_bottomRows_eq {t t' : Fin n → Fˣ}
    (h : ∀ k : Fin n, ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) =
      ∏ a : Fin (k.val + 1), (t' (bottomRows k a) : F)) : t = t' := by sorry
