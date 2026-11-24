-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_shear_hit
-- name    : GlobalTheory.HopfQuot.shear_hit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:52.709279+00:00
-- url     : https://prove2.me/theorems/2f386fb5-f2d4-4720-92ba-b7f19a9b8fe5
-- title:
--   Hopf Quot: shear hit
-- statement:
--   The Hopf Quot construction uses the shear hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L90-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L90-L121

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

theorem GlobalTheory.HopfQuot.shear_hit (f : Λ →ₗ[R] R) (z : Λ ⊗[R] Λ) :
    shear R Λ ((hit f).baseChange Λ z) = (hit f).baseChange Λ (shear R Λ z) := by sorry
