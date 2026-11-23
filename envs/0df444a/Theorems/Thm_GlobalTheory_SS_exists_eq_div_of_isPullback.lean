-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_eq_div_of_isPullback
-- name    : GlobalTheory.SS.exists_eq_div_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:45.760454+00:00
-- url     : https://prove2.me/theorems/9bfda63e-0370-405b-8195-f009aa6d429a
-- title:
--   SS: exists eq div of is Pullback
-- statement:
--   The SS construction uses the exists eq div of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsEqDivOfIsPullback.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsEqDivOfIsPullback.lean#L7-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.SS

theorem GlobalTheory.SS.exists_eq_div_of_isPullback : ∀ (P X Y S : Scheme.{0}) [IsAffine S] (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S), IsPullback p q f g → ∀ (z : P) (U : X.Opens) (U' : Y.Opens) (W : P.Opens), p z ∈ U → q z ∈ U' → z ∈ W → ∃ (V : X.Opens) (V' : Y.Opens) (W' : P.Opens) (h₁ : W' ≤ p ⁻¹ᵁ V) (h₂ : W' ≤ q ⁻¹ᵁ V'), V ≤ U ∧ V' ≤ U' ∧ W' ≤ W ∧ z ∈ W' ∧ ∀ τ : Γ(P, W'), ∃ a ∈ Subring.closure (Set.range (p.appLE V W' h₁).hom ∪ Set.range (q.appLE V' W' h₂).hom), ∃ b ∈ Subring.closure (Set.range (p.appLE V W' h₁).hom ∪ Set.range (q.appLE V' W' h₂).hom), IsUnit a ∧ τ * a = b := by sorry
