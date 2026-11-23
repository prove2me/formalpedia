-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_lam_apply
-- name    : GlobalTheory.HopfQuot.lam_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:17.423729+00:00
-- url     : https://prove2.me/theorems/13e0eee3-dc7a-4af7-8c10-065ee07a1849
-- title:
--   Hopf Quot: lam apply
-- statement:
--   The Hopf Quot construction uses the lam apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L126-L128

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

theorem GlobalTheory.HopfQuot.lam_apply (e : ι → Λ) (c : ι → Λ →ₗ[R] R) (f : Λ →ₗ[R] R) (x : Λ) :
    lam e c f x = tr e c (hit f ∘ₗ LinearMap.mulLeft R x) := by sorry
