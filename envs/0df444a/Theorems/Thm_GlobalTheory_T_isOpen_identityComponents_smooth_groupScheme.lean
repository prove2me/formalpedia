-- Prove2me | Theorems.Thm_GlobalTheory_T_isOpen_identityComponents_smooth_groupScheme
-- name    : GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:25.172455+00:00
-- url     : https://prove2.me/theorems/980f6b43-8b9f-4048-944f-eb26798fb24e
-- title:
--   T: is Open identity Components smooth group Scheme
-- statement:
--   The T construction uses the is Open identity Components smooth group Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIdentityComponentsSmoothGroupSchemeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIdentityComponentsSmoothGroupSchemeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIdentityComponentsSmoothGroupScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIdentityComponentsSmoothGroupSchemeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by sorry
