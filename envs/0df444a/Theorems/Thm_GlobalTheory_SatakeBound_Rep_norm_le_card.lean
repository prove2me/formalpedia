-- Prove2me | Theorems.Thm_GlobalTheory_SatakeBound_Rep_norm_le_card
-- name    : GlobalTheory.SatakeBound.Rep.norm_le_card
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:08.496951+00:00
-- url     : https://prove2.me/theorems/91a07d24-41a9-4ea6-882f-cf140aed8b6f
-- title:
--   Rep: norm le card
-- statement:
--   The Rep construction uses the norm le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeCard.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeCard.lean#L18-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound
open GlobalTheory GlobalTheory.SatakeBound GlobalTheory.SatakeBound.Rep
variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.SatakeBound.Rep.norm_le_card {ι : Type} {π : Representation ℂ G V} (hπ : IsUnitarisable π) {v : V} (hv : v ≠ 0)
    (S : Finset ι) (g : ι → G) (l : ℂ) (h : ∑ c ∈ S, π (g c) v = l • v) : ‖l‖ ≤ S.card := by sorry
