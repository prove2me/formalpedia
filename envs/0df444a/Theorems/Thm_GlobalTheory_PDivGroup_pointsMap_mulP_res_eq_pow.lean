-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_pointsMap_mulP_res_eq_pow
-- name    : GlobalTheory.PDivGroup.pointsMap_mulP_res_eq_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:53:30.155439+00:00
-- url     : https://prove2.me/theorems/f5ccd41b-a744-4ecf-81fd-7f43229658c2
-- title:
--   PDiv Group: points Map mul P res eq pow
-- statement:
--   The PDiv Group construction uses the points Map mul P res eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L188-L191

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

theorem GlobalTheory.PDivGroup.pointsMap_mulP_res_eq_pow (n : ℕ) (x : WithConv (G.A n →ₐ[O] B)) :
    pointsMap B (G.mulP n) (pointsMap B (G.res n) x) = x ^ p := by sorry
