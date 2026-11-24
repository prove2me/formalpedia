-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_res_inf_injective
-- name    : GlobalTheory.PrimeSection.res_inf_injective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:48.066876+00:00
-- url     : https://prove2.me/theorems/74292e00-62ef-4ba6-a5ab-bdbbaff6ad21
-- title:
--   Prime Section: res inf injective
-- statement:
--   The Prime Section construction uses the res inf injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L62-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} [IsIntegral X]

theorem GlobalTheory.PrimeSection.res_inf_injective {D : X.Opens} (hD : genericPoint X ∈ D) (W : X.Opens) :
    Function.Injective (X.presheaf.map (homOfLE (inf_le_left : W ⊓ D ≤ W)).op) := by sorry
