-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsOrd_cycNorm
-- name    : GroundTheory.LocalField.unitsOrd_cycNorm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:57.185718+00:00
-- url     : https://prove2.me/theorems/3548689b-5233-584e-b160-02507cb31666
-- title:
--   Local Field: units Ord cyc Norm
-- statement:
--   The Local Field construction uses the units Ord cyc Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L125-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L125-L131

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

theorem GroundTheory.LocalField.unitsOrd_cycNorm (x : Additive Lˣ) :
    unitsOrd L (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) x) =
      cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) (unitsOrd L x) := by sorry
