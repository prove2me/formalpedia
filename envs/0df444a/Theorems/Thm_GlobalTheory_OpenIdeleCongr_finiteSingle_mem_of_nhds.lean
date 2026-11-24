-- Prove2me | Theorems.Thm_GlobalTheory_OpenIdeleCongr_finiteSingle_mem_of_nhds
-- name    : GlobalTheory.OpenIdeleCongr.finiteSingle_mem_of_nhds
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:01.043317+00:00
-- url     : https://prove2.me/theorems/2315a88b-5059-4739-831a-46b6c8e3bdec
-- title:
--   Open Idele Congr: finite Single mem of nhds
-- statement:
--   The Open Idele Congr construction uses the finite Single mem of nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L51-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L51-L101

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

theorem GlobalTheory.OpenIdeleCongr.finiteSingle_mem_of_nhds (Vf : Set (FiniteAdeleRing (𝓞 F) F)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (y : v.adicCompletion F),
      y ∈ v.adicCompletionIntegers F → (v ∈ S → Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ))) →
      finiteSingle F v y ∈ Vf := by sorry
