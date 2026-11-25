-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_ptsMap_res_mulP
-- name    : GlobalTheory.PDivGroup.ptsMap_res_mulP
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:07:56.403798+00:00
-- url     : https://prove2.me/theorems/67945b8c-4fe8-4c47-9323-54115a014d2b
-- title:
--   PDiv Group: pts Map res mul P
-- statement:
--   The PDiv Group construction uses the pts Map res mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L183-L186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable {B : Type} [CommRing B] [Algebra O B]

theorem GlobalTheory.PDivGroup.ptsMap_res_mulP (n : ℕ) (x : WithConv (G.A (n + 1) →ₐ[O] B)) :
    pointsMap B (G.res n) (pointsMap B (G.mulP n) x) = x ^ p := by sorry
