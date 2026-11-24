-- Prove2me | Theorems.Thm_GlobalTheory_scheme_homOfLE_apply_mk
-- name    : GlobalTheory.scheme_homOfLE_apply_mk
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:20:30.004971+00:00
-- url     : https://prove2.me/theorems/547464aa-704c-493a-bd34-70faa1d633f5
-- title:
--   Global Theory: scheme hom Of LE apply mk
-- statement:
--   The Global Theory construction uses the scheme hom Of LE apply mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpacePullbackFieldOfIrreducibleCover.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpacePullbackFieldOfIrreducibleCover.lean#L21-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackFieldOfIrreducibleCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.scheme_homOfLE_apply_mk {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (x : X) (hx : x ∈ V) :
    (X.homOfLE e) ⟨x, hx⟩ = ⟨x, e hx⟩ := by sorry
