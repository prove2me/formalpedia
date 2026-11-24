-- Prove2me | Theorems.Thm_GlobalTheory_OpenIdeleCongr_exists_ne_zero_lt_val_subset_of_mem_nhds
-- name    : GlobalTheory.OpenIdeleCongr.exists_ne_zero_lt_val_subset_of_mem_nhds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:34.115021+00:00
-- url     : https://prove2.me/theorems/aef6fcc9-b4f4-4feb-b44d-f3b959e62bdb
-- title:
--   Open Idele Congr: exists ne zero lt val subset of mem nhds
-- statement:
--   The Open Idele Congr construction uses the exists ne zero lt val subset of mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L13-L25

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenIdeleSubgroupContainsCongruenceUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.OpenIdeleCongr
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.OpenIdeleCongr.exists_ne_zero_lt_val_subset_of_mem_nhds {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] {s : Set K} {x : K} :
    s ∈ nhds x → ∃ c : K, c ≠ 0 ∧ {y | Valued.v (y - x) < Valued.v c} ⊆ s := by sorry
