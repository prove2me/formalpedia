-- Prove2me | Theorems.Thm_GlobalTheory_ResDegPlace_finrank_eq_of_surjective
-- name    : GlobalTheory.ResDegPlace.finrank_eq_of_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:47.701881+00:00
-- url     : https://prove2.me/theorems/25f3a494-b173-4b79-b132-c01938e88a3b
-- title:
--   Res Deg Place: finrank eq of surjective
-- statement:
--   The Res Deg Place construction uses the finrank eq of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FdegEqFinrankResidueField.lean#L13-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FdegEqFinrankResidueField.lean#L13-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResDegPlace
open IsLocalRing

theorem GlobalTheory.ResDegPlace.finrank_eq_of_surjective {S₀ S k K k' K' : Type*} [CommRing S₀] [CommRing S] [Field k]
    [Field K] [Field k'] [Field K'] [Algebra k K] [Algebra k' K'] (j : S₀ →+* S)
    (p₀ : S₀ →+* k) (q₀ : S₀ →+* k') (p : S →+* K) (q : S →+* K')
    (hp₀ : Function.Surjective p₀) (hq₀ : Function.Surjective q₀)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : ∀ x, p x = 0 ↔ q x = 0)
    (h₁ : ∀ r, algebraMap k K (p₀ r) = p (j r)) (h₂ : ∀ r, algebraMap k' K' (q₀ r) = q (j r)) :
    Module.finrank k K = Module.finrank k' K' := by sorry
