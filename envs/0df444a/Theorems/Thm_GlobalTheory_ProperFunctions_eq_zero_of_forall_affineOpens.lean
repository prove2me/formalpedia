-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_eq_zero_of_forall_affineOpens
-- name    : GlobalTheory.ProperFunctions.eq_zero_of_forall_affineOpens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:46.471111+00:00
-- url     : https://prove2.me/theorems/8c226dc5-c945-4b91-a8b1-e0417f07ef7b
-- title:
--   Proper Functions: eq zero of forall affine Opens
-- statement:
--   The Proper Functions construction uses the eq zero of forall affine Opens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L138-L141

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

theorem GlobalTheory.ProperFunctions.eq_zero_of_forall_affineOpens (x : Γ(X, ⊤))
    (h : ∀ U : X.affineOpens, X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x = 0) : x = 0 := by sorry
