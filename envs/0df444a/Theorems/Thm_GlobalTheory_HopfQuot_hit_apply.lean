-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_hit_apply
-- name    : GlobalTheory.HopfQuot.hit_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:03.90757+00:00
-- url     : https://prove2.me/theorems/54e0bca3-88fe-4c0c-b133-b8f20dc6ae52
-- title:
--   Hopf Quot: hit apply
-- statement:
--   The Hopf Quot construction uses the hit apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L46-L46

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

theorem GlobalTheory.HopfQuot.hit_apply (f : Λ →ₗ[R] R) (y : Λ) : hit f y = ev Λ f (Coalgebra.comul y) := by sorry
