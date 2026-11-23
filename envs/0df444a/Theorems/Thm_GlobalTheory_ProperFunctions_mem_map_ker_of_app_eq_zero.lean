-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_app_eq_zero
-- name    : GlobalTheory.ProperFunctions.mem_map_ker_of_app_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:41.192031+00:00
-- url     : https://prove2.me/theorems/04ee8f19-664b-4f06-9c50-56c147917a7c
-- title:
--   Proper Functions: mem map ker of app eq zero
-- statement:
--   The Proper Functions construction uses the mem map ker of app eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L128-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}

theorem GlobalTheory.ProperFunctions.mem_map_ker_of_app_eq_zero (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p]
    {U : X.Opens} (hU : IsAffineOpen U) (x : Γ(X, U)) (hx : g.app U x = 0) :
    x ∈ (RingHom.ker f.appTop.hom).map (p.appLE ⊤ U (le_preimage_top p U)).hom := by sorry
