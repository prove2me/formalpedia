-- Prove2me | Theorems.Thm_GlobalTheory_T_smoothContragredient_irreducible_and_reflexive
-- name    : GlobalTheory.T.smoothContragredient_irreducible_and_reflexive
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:56.949648+00:00
-- url     : https://prove2.me/theorems/04d78d6b-5981-45bf-9e3b-95e677fe285e
-- title:
--   T: smooth Contragredient irreducible and reflexive
-- statement:
--   The T construction uses the smooth Contragredient irreducible and reflexive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexiveStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexiveStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.smoothContragredient_irreducible_and_reflexive : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → (π.IsIrreducible → (contra π).IsIrreducible) ∧ Nonempty (π.Equiv (contra (contra π))) ∧ (Nonempty ((contra π).Equiv (contra π')) → Nonempty (π.Equiv π')) := by sorry
