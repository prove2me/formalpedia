-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsOrd_cycSubOne
-- name    : GroundTheory.LocalField.unitsOrd_cycSubOne
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:17.43369+00:00
-- url     : https://prove2.me/theorems/750e003c-e96a-4bda-8459-b3cd46dd0096
-- title:
--   Local Field: units Ord cyc Sub One
-- statement:
--   The Local Field construction uses the units Ord cyc Sub One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L118-L123

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.unitsOrd_cycSubOne (τ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    unitsOrd L (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) τ x) =
      cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) τ (unitsOrd L x) := by sorry
