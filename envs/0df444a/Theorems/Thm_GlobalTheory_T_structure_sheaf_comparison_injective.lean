-- Prove2me | Theorems.Thm_GlobalTheory_T_structure_sheaf_comparison_injective
-- name    : GlobalTheory.T.structure_sheaf_comparison_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:45:24.933911+00:00
-- url     : https://prove2.me/theorems/7fafd925-9e04-5421-a000-97e44313f312
-- title:
--   T: structure sheaf comparison injective
-- statement:
--   The T construction uses the structure sheaf comparison injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafComparisonInjectiveStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafComparisonInjectiveStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafComparisonInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafComparisonInjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.structure_sheaf_comparison_injective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Function.Injective (cmpO s) := by sorry
