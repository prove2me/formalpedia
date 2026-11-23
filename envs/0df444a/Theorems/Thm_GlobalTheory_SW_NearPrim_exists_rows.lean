-- Prove2me | Theorems.Thm_GlobalTheory_SW_NearPrim_exists_rows
-- name    : GlobalTheory.SW.NearPrim.exists_rows
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:48:33.098327+00:00
-- url     : https://prove2.me/theorems/4b1c6034-4805-4dfb-aedb-1d0505c2252c
-- title:
--   Near Prim: exists rows
-- statement:
--   The Near Prim construction uses the exists rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsNearlyPrimitive.lean#L88-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsNearlyPrimitive.lean#L88-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.NearPrim

theorem GlobalTheory.SW.NearPrim.exists_rows {E : Type} [Field E] [NumberField E] {k : ℕ} (L : AddSubgroup (Fin k → E))
    (hO : ∀ s : Fin k → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L) (d : ℤ) (hd : d ≠ 0)
    (hL : ∀ s ∈ L, ∀ i, IsIntegral ℤ ((d : E) * s i)) (C : ℝ)
    (hC : ∀ x : E, ∃ y : E, IsIntegral ℤ y ∧ ‖canonicalEmbedding E (x - y)‖ ≤ C) (i : Fin k) :
    ∃ a ∈ L, (∀ j, i < j → a j = 0) ∧ a i ≠ 0 ∧ (∀ j, ‖canonicalEmbedding E (a j)‖ ≤ max 1 C) ∧
      ∀ s ∈ L, (∀ j, i < j → s j = 0) → s i ≠ 0 →
        ‖canonicalEmbedding E (a i)‖ ≤ ‖canonicalEmbedding E (s i)‖ := by sorry
