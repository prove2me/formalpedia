-- Prove2me | Theorems.Thm_GlobalTheory_isIrreducible_toRepresentation_of_isAtom
-- name    : GlobalTheory.isIrreducible_toRepresentation_of_isAtom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:58:51.701633+00:00
-- url     : https://prove2.me/theorems/46bd8e16-9973-470a-ac04-1aec3e2c8cad
-- title:
--   Global Theory: is Irreducible to Representation of is Atom
-- statement:
--   The Global Theory construction uses the is Irreducible to Representation of is Atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L245-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L245-L265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜]

theorem GlobalTheory.isIrreducible_toRepresentation_of_isAtom {F G V : Type*} [Field F] [Monoid G]
    [AddCommGroup V] [Module F V] {ρ : Representation F G V} {U : Subrepresentation ρ}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by sorry
