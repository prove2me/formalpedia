-- Prove2me | Theorems.Thm_GlobalTheory_EisBL_NilAlg_proj_add
-- name    : GlobalTheory.EisBL.NilAlg.proj_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:24.935201+00:00
-- url     : https://prove2.me/theorems/8954b157-b742-4f85-ba5b-64aef739ff94
-- title:
--   Nil Alg: proj add
-- statement:
--   The Nil Alg construction uses the proj add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L97-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.EisBL.NilAlg.proj_add (c : B →+* B) (J K : Matrix n n B) (h : B) (X Y : Matrix n n B) :
    proj c J K h (X + Y) = proj c J K h X + proj c J K h Y := by sorry
