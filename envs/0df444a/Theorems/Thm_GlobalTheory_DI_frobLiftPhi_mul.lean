-- Prove2me | Theorems.Thm_GlobalTheory_DI_frobLiftPhi_mul
-- name    : GlobalTheory.DI.frobLiftPhi_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:16.685871+00:00
-- url     : https://prove2.me/theorems/0554af4e-f9b9-4dfb-b4fa-e529c02259e2
-- title:
--   DI: frob Lift Phi mul
-- statement:
--   The DI construction uses the frob Lift Phi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobLiftPsiNatCastMul.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobLiftPsiNatCastMul.lean#L150-L154

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

theorem GlobalTheory.DI.frobLiftPhi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (a b : K) :
    frobLiftPhi hL hF (a * b) = a ^ p • frobLiftPhi hL hF b + b ^ p • frobLiftPhi hL hF a := by sorry
