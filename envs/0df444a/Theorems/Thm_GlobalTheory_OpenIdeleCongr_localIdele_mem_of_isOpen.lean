-- Prove2me | Theorems.Thm_GlobalTheory_OpenIdeleCongr_localIdele_mem_of_isOpen
-- name    : GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:53.344795+00:00
-- url     : https://prove2.me/theorems/fc19533f-4768-4654-9178-e2ca0a06578a
-- title:
--   Open Idele Congr: local Idele mem of is Open
-- statement:
--   The Open Idele Congr construction uses the local Idele mem of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L109-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L109-L146

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

theorem GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen (V : Subgroup (Ideles F)) (hV : IsOpen (V : Set (Ideles F))) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (x : (v.adicCompletion F)ˣ),
      Valued.v (x : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) → localIdele F v x ∈ V := by sorry
