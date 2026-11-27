-- Prove2me | Theorems.Thm_GlobalTheory_preimage_eq_of_finite_appLE
-- name    : GlobalTheory.preimage_eq_of_finite_appLE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:19.867471+00:00
-- url     : https://prove2.me/theorems/68baddd6-9c09-5946-bc5c-963eeb09db62
-- title:
--   Global Theory: preimage eq of finite app LE
-- statement:
--   The Global Theory construction uses the preimage eq of finite app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreimageEqOfFiniteAppLE.lean#L6-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreimageEqOfFiniteAppLE.lean#L6-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfFiniteAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory

theorem GlobalTheory.preimage_eq_of_finite_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π] {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → IsAffineOpen V → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (π.appLE U V h).hom.Finite → π ⁻¹ᵁ U = V := by sorry
