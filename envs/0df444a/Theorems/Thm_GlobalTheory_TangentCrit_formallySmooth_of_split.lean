-- Prove2me | Theorems.Thm_GlobalTheory_TangentCrit_formallySmooth_of_split
-- name    : GlobalTheory.TangentCrit.formallySmooth_of_split
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:02.362923+00:00
-- url     : https://prove2.me/theorems/f4806c71-81b3-4926-8f28-27db2288c5f8
-- title:
--   Tangent Crit: formally Smooth of split
-- statement:
--   The Tangent Crit construction uses the formally Smooth of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L72-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L72-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
variable {R A B k : Type*} [CommRing R] [CommRing A] [CommRing B]

theorem GlobalTheory.TangentCrit.formallySmooth_of_split [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallySmooth R B] (r : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R])
    (hr : r ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id) :
    Algebra.FormallySmooth A B := by sorry
