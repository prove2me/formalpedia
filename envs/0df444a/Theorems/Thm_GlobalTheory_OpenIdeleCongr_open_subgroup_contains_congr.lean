-- Prove2me | Theorems.Thm_GlobalTheory_OpenIdeleCongr_open_subgroup_contains_congr
-- name    : GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:18.067092+00:00
-- url     : https://prove2.me/theorems/66571588-e423-405d-b590-c2542fd97d6a
-- title:
--   Open Idele Congr: open subgroup contains congr
-- statement:
--   The Open Idele Congr construction uses the open subgroup contains congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L148-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L148-L182

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

theorem GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)),
    IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧
      (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧
      ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by sorry
