-- Prove2me | Theorems.Thm_GlobalTheory_SW_NearPrim_exists_den
-- name    : GlobalTheory.SW.NearPrim.exists_den
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:46.146914+00:00
-- url     : https://prove2.me/theorems/466b8fae-3060-4003-955d-9406e36af4c1
-- title:
--   Near Prim: exists den
-- statement:
--   The Near Prim construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsNearlyPrimitive.lean#L68-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsNearlyPrimitive.lean#L68-L86

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

theorem GlobalTheory.SW.NearPrim.exists_den {E : Type} [Field E] [NumberField E] {k : ℕ} {m : Type} [Fintype m]
    (W : Matrix (Fin k) m E) (hW : LinearIndependent E (fun i => W i)) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ s : Fin k → E, (∀ j, IsIntegral ℤ ((s ᵥ* W) j)) →
      ∀ i, IsIntegral ℤ ((d : E) * s i) := by sorry
