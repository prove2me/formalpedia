-- Prove2me | Theorems.Thm_GlobalTheory_Published_HasseNormSt_of_isSquare
-- name    : GlobalTheory.Published.HasseNormSt.of_isSquare
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:44.815274+00:00
-- url     : https://prove2.me/theorems/795b7f49-9a28-43df-b8e1-cc5e2c4ec4e2
-- title:
--   Hasse Norm St: of is Square
-- statement:
--   The Hasse Norm St construction uses the of is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/ExistsNormTensor.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/ExistsNormTensor.lean#L18-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.HasseNormSt
open scoped TensorProduct

theorem GlobalTheory.Published.HasseNormSt.of_isSquare {F : Type*} [Field F] [CharZero F] {δ : F} (h0 : δ ≠ 0) (hδ : _root_.IsSquare δ) (x : F) :
    ∃ a b : F, x = a ^ 2 - δ * b ^ 2 := by sorry
