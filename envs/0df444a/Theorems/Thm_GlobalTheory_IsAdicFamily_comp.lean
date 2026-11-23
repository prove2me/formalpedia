-- Prove2me | Theorems.Thm_GlobalTheory_IsAdicFamily_comp
-- name    : GlobalTheory.IsAdicFamily.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:36.996355+00:00
-- url     : https://prove2.me/theorems/253e0d9d-9817-4ed0-82d0-8ff326e8b3bb
-- title:
--   Is Adic Family: comp
-- statement:
--   The Is Adic Family construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L223-L225

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
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}

theorem GlobalTheory.IsAdicFamily.comp {X Y : Scheme.{u}} {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily I f) (p : X ⟶ Y) : IsAdicFamily I fun n => f n ≫ p := by sorry
