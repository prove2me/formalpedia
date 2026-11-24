-- Prove2me | Theorems.Thm_GlobalTheory_T_smulInvariantMeasure_sheared_product_pairGroup
-- name    : GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:19.465973+00:00
-- url     : https://prove2.me/theorems/9ecf538d-88ac-4332-b71c-fce9461a8523
-- title:
--   T: smul Invariant Measure sheared product pair Group
-- statement:
--   The T construction uses the smul Invariant Measure sheared product pair Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmulInvariantMeasureShearedProductPairGroupStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmulInvariantMeasureShearedProductPairGroupStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulInvariantMeasureShearedProductPairGroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulInvariantMeasureShearedProductPairGroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N), κ.IsHaarMeasure → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → SMulInvariantMeasure (GlobalTheory.UnfoldNormal.pairGroup Γ N hN) (H × H) ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)) := by sorry
