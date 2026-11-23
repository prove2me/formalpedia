-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
-- name    : GlobalTheory.HopfQuot.ev_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:18.687925+00:00
-- url     : https://prove2.me/theorems/ba83c2db-3b03-4f5d-b965-2e459bbcf9b0
-- title:
--   Hopf Quot: ev tmul
-- statement:
--   The Hopf Quot construction uses the ev tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L34-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ : Type*} [CommRing R] [AddCommGroup Λ] [Module R Λ]

theorem GlobalTheory.HopfQuot.ev_tmul (B : Type*) [CommRing B] [Algebra R B] (f : Λ →ₗ[R] R) (b : B) (x : Λ) :
    ev B f (b ⊗ₜ x) = f x • b := by sorry
