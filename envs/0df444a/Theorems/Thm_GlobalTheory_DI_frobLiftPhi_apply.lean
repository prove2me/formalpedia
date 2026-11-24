-- Prove2me | Theorems.Thm_GlobalTheory_DI_frobLiftPhi_apply
-- name    : GlobalTheory.DI.frobLiftPhi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:54:09.241224+00:00
-- url     : https://prove2.me/theorems/b0fb0913-b893-499d-b27f-f40b7658003b
-- title:
--   DI: frob Lift Phi apply
-- statement:
--   The DI construction uses the frob Lift Phi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobLiftPsiNatCastMul.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobLiftPsiNatCastMul.lean#L146-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehlerStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobLiftPsiNatCastMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K]
variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)
variable {p π F}

theorem GlobalTheory.DI.frobLiftPhi_apply (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    frobLiftPhi hL hF (π z) = frobLiftPsi p π F hL hF z := by sorry
