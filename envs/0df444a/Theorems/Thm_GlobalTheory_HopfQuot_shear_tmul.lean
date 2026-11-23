-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_shear_tmul
-- name    : GlobalTheory.HopfQuot.shear_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:13.647276+00:00
-- url     : https://prove2.me/theorems/e9b8c0e5-e269-418e-af86-6543782b0e13
-- title:
--   Hopf Quot: shear tmul
-- statement:
--   The Hopf Quot construction uses the shear tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L53-L54

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

theorem GlobalTheory.HopfQuot.shear_tmul (x y : Λ) : shear R Λ (x ⊗ₜ y) = x • Coalgebra.comul (R := R) y := by sorry
