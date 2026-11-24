-- Prove2me | Theorems.Thm_GlobalTheory_OpenIdeleCongr_exists_exp_of_nhds
-- name    : GlobalTheory.OpenIdeleCongr.exists_exp_of_nhds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:38.069911+00:00
-- url     : https://prove2.me/theorems/ef3724d9-a4cb-4c03-874d-e28d5e2ba950
-- title:
--   Open Idele Congr: exists exp of nhds
-- statement:
--   The Open Idele Congr construction uses the exists exp of nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L27-L39

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

theorem GlobalTheory.OpenIdeleCongr.exists_exp_of_nhds (v : HeightOneSpectrum (𝓞 F)) (u : Set (v.adicCompletion F)) (hu : u ∈ nhds 1) :
    ∃ M : ℕ, ∀ y : v.adicCompletion F, Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → y ∈ u := by sorry
