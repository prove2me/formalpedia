-- Prove2me | Theorems.Thm_GroundTheory_LocalField_cycHerbrand_integerUnits_eq_one_of_subgroup
-- name    : GroundTheory.LocalField.cycHerbrand_integerUnits_eq_one_of_subgroup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:16:51.218604+00:00
-- url     : https://prove2.me/theorems/00805725-a695-4635-82da-5edbc7caa3d1
-- title:
--   Local Field: cyc Herbrand integer Units eq one of subgroup
-- statement:
--   The Local Field construction uses the cyc Herbrand integer Units eq one of subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L161-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L161-L172

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
variable {σ : L ≃ₐ[K] L}

theorem GroundTheory.LocalField.cycHerbrand_integerUnits_eq_one_of_subgroup (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (V : Subgroup 𝒪[L]ˣ) [V.FiniteIndex] [MulDistribMulAction (L ≃ₐ[K] L) V]
    (hV : ∀ (g : L ≃ₐ[K] L) (v : V), ((g • v : V) : 𝒪[L]ˣ) = g • (v : 𝒪[L]ˣ))
    [Subsingleton (TateZero (L ≃ₐ[K] L) V)] [Subsingleton (TateNegOne (L ≃ₐ[K] L) V)] :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by sorry
