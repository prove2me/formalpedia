-- Prove2me | Theorems.Thm_GlobalTheory_exists_local_lift_of_smooth
-- name    : GlobalTheory.exists_local_lift_of_smooth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:19.467318+00:00
-- url     : https://prove2.me/theorems/289a717b-9955-44ea-a22c-1b2ea9bfe48e
-- title:
--   Global Theory: exists local lift of smooth
-- statement:
--   The Global Theory construction uses the exists local lift of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L139-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L139-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.exists_local_lift_of_smooth {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (g : T₀ ⟶ X) (h : T ⟶ S) (w : g ≫ f = i ≫ h) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (l : W.toScheme ⟶ X), l ≫ f = W.ι ≫ h ∧
      (i ∣_ W) ≫ l = (i ⁻¹ᵁ W).ι ≫ g := by sorry
