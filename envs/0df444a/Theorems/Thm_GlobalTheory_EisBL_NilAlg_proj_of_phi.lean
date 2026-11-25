-- Prove2me | Theorems.Thm_GlobalTheory_EisBL_NilAlg_proj_of_phi
-- name    : GlobalTheory.EisBL.NilAlg.proj_of_phi
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:42.97581+00:00
-- url     : https://prove2.me/theorems/15c5cda0-617c-4c4a-9f76-e2cf86a1a6a4
-- title:
--   Nil Alg: proj of phi
-- statement:
--   The Nil Alg construction uses the proj of phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L111-L114

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

theorem GlobalTheory.EisBL.NilAlg.proj_of_phi (c : B →+* B) {J K : Matrix n n B} (hJK : J * K = 1) (hKJ : K * J = 1) (h : B) (h2 : h * 2 = 1)
    (X : Matrix n n B) (hX : phi c J X = 0) : proj c J K h X = X := by sorry
