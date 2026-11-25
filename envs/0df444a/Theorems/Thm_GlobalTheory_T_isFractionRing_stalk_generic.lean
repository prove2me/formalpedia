-- Prove2me | Theorems.Thm_GlobalTheory_T_isFractionRing_stalk_generic
-- name    : GlobalTheory.T.isFractionRing_stalk_generic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:33:57.019557+00:00
-- url     : https://prove2.me/theorems/053e39e3-1a3c-4f42-9890-e4d7ab5ec633
-- title:
--   T: is Fraction Ring stalk generic
-- statement:
--   The T construction uses the is Fraction Ring stalk generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsFractionRingStalkGenericStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsFractionRingStalkGenericStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsFractionRingStalkGeneric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsFractionRingStalkGenericStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isFractionRing_stalk_generic : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x), IsDomain (X.presheaf.stalk x) → (∀ y, y ⤳ ξ → y = ξ) → @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _ (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) := by sorry
