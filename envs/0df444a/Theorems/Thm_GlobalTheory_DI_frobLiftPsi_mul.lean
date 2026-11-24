-- Prove2me | Theorems.Thm_GlobalTheory_DI_frobLiftPsi_mul
-- name    : GlobalTheory.DI.frobLiftPsi_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:41.6658+00:00
-- url     : https://prove2.me/theorems/12f3af42-f434-43ad-a3fd-3fc1cf6c9857
-- title:
--   DI: frob Lift Psi mul
-- statement:
--   The DI construction uses the frob Lift Psi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobLiftPsiNatCastMul.lean#L99-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobLiftPsiNatCastMul.lean#L99-L116

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

theorem GlobalTheory.DI.frobLiftPsi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z * z') =
      π z ^ p • frobLiftPsi p π F hL hF z' + π z' ^ p • frobLiftPsi p π F hL hF z := by sorry
