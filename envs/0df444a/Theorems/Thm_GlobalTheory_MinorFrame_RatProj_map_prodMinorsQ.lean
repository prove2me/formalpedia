-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_RatProj_map_prodMinorsQ
-- name    : GlobalTheory.MinorFrame.RatProj.map_prodMinorsQ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:39.223819+00:00
-- url     : https://prove2.me/theorems/8f3e027a-b6ea-485a-8489-14405eefd721
-- title:
--   Rat Proj: map prod Minors Q
-- statement:
--   The Rat Proj construction uses the map prod Minors Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsRationalFockProjectionMaximalMinors.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsRationalFockProjectionMaximalMinors.lean#L74-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsRationalFockProjectionMaximalMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RatProj
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.RatProj.map_prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) :
    map (algebraMap ℚ ℂ) (prodMinorsQ T) = prodMinors T := by sorry
