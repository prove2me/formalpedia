-- Prove2me | Theorems.Thm_GlobalTheory_T_schemeTheoreticallyDominant_of_germ_injective
-- name    : GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:56:52.31824+00:00
-- url     : https://prove2.me/theorems/30dc076e-a0ad-42bc-8baf-aaadd651b574
-- title:
--   T: scheme Theoretically Dominant of germ injective
-- statement:
--   The T construction uses the scheme Theoretically Dominant of germ injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchemeTheoreticallyDominantOfGermInjectiveStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchemeTheoreticallyDominantOfGermInjectiveStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchemeTheoreticallyDominantOfGermInjective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchemeTheoreticallyDominantOfGermInjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens),
    (∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) →
    IsSchemeTheoreticallyDominant W.ι := by sorry
