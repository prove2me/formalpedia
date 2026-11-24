-- Prove2me | Theorems.Thm_GlobalTheory_TangentCrit_formallySmooth_of_dual_lift
-- name    : GlobalTheory.TangentCrit.formallySmooth_of_dual_lift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:01:54.451801+00:00
-- url     : https://prove2.me/theorems/8cf290ad-8813-48c1-83a7-92727c359add
-- title:
--   Tangent Crit: formally Smooth of dual lift
-- statement:
--   The Tangent Crit construction uses the formally Smooth of dual lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L94-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L94-L122

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

theorem GlobalTheory.TangentCrit.formallySmooth_of_dual_lift [Field k] [IsLocalRing B] (α : R →+* A) (β : A →+* B)
    (hA : α.EssFiniteType) (hB : (β.comp α).EssFiniteType) (hs : (β.comp α).FormallySmooth)
    (x : B →+* k) [IsLocalHom x]
    (H : ∀ ψ : A →+* DualNumber k, (∀ a, (ψ a).fst = x (β a)) → (∀ r, (ψ (α r)).snd = 0) →
      ∃ φ : B →+* DualNumber k, (∀ b, (φ b).fst = x b) ∧ ∀ a, φ (β a) = ψ a) :
    β.FormallySmooth := by sorry
