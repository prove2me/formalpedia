-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_shear_surjective
-- name    : GlobalTheory.HopfQuot.shear_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:29.969863+00:00
-- url     : https://prove2.me/theorems/90f04e6e-9275-4013-9718-6c60a4e242bf
-- title:
--   Hopf Quot: shear surjective
-- statement:
--   The Hopf Quot construction uses the shear surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L56-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L56-L88

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
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]

theorem GlobalTheory.HopfQuot.shear_surjective : Function.Surjective (shear R Λ) := by sorry
