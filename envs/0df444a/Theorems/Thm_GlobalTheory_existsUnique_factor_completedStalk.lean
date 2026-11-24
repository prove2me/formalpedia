-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_factor_completedStalk
-- name    : GlobalTheory.existsUnique_factor_completedStalk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:26.585865+00:00
-- url     : https://prove2.me/theorems/61dd421a-77f4-42f6-8c5f-a2a5623877f4
-- title:
--   Global Theory: exists Unique factor completed Stalk
-- statement:
--   The Global Theory construction uses the exists Unique factor completed Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L142-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L142-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
omit [IsLocalRing R]

theorem GlobalTheory.existsUnique_factor_completedStalk (I : Ideal R) [IsAdicComplete I R]
    {f : Spec (.of R) ⟶ X} {x : X}
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f)
    (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    (hk : ∃ k : ℕ, (maximalIdeal (X.presheaf.stalk x)).map φ.hom ^ k ≤ I) :
    ∃! ψ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+* R,
      Spec.map (CommRingCat.ofHom ψ) ≫ fromSpecCompletedStalk X x = f := by sorry
