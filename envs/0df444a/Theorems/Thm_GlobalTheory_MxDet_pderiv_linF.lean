-- Prove2me | Theorems.Thm_GlobalTheory_MxDet_pderiv_linF
-- name    : GlobalTheory.MxDet.pderiv_linF
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:30:14.264551+00:00
-- url     : https://prove2.me/theorems/9cee9a35-f7d6-456a-8892-28809ba3666a
-- title:
--   Mx Det: pderiv lin F
-- statement:
--   The Mx Det construction uses the pderiv lin F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean#L14-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.MxDet

theorem GlobalTheory.MxDet.pderiv_linF {ι : Type} [Fintype ι] (x : ι → ℝ) (j : ι) :
    MvPolynomial.pderiv j (linF x) = MvPolynomial.C (x j) := by sorry
