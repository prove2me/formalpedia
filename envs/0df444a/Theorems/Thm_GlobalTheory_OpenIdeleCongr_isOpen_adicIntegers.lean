-- Prove2me | Theorems.Thm_GlobalTheory_OpenIdeleCongr_isOpen_adicIntegers
-- name    : GlobalTheory.OpenIdeleCongr.isOpen_adicIntegers
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:39:48.926605+00:00
-- url     : https://prove2.me/theorems/52894066-28e9-438c-94d2-cd39968909e1
-- title:
--   Open Idele Congr: is Open adic Integers
-- statement:
--   The Open Idele Congr construction uses the is Open adic Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenIdeleSubgroupContainsCongruenceUnits.lean#L47-L49

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

theorem GlobalTheory.OpenIdeleCongr.isOpen_adicIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by sorry
