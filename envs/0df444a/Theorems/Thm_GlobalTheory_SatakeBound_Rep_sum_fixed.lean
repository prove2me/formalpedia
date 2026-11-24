-- Prove2me | Theorems.Thm_GlobalTheory_SatakeBound_Rep_sum_fixed
-- name    : GlobalTheory.SatakeBound.Rep.sum_fixed
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:04.524047+00:00
-- url     : https://prove2.me/theorems/52ee0c1d-3321-4650-9b30-d15463a24935
-- title:
--   Rep: sum fixed
-- statement:
--   The Rep construction uses the sum fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeCard.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeCard.lean#L33-L43

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

theorem GlobalTheory.SatakeBound.Rep.sum_fixed (ρ : Representation ℂ G X) (K : Subgroup G) {w : X} (hw : ∀ x ∈ K, ρ x w = w)
    (S : Finset (G ⧸ K)) (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) (x : G) (hx : x ∈ K) :
    ρ x (∑ c ∈ S, ρ c.out w) = ∑ c ∈ S, ρ c.out w := by sorry
