-- Prove2me | Theorems.Thm_GlobalTheory_EisBL_NilAlg_proj_map
-- name    : GlobalTheory.EisBL.NilAlg.proj_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:34.812313+00:00
-- url     : https://prove2.me/theorems/29dd288a-62af-5c44-a837-a6d55b2b84cd
-- title:
--   Nil Alg: proj map
-- statement:
--   The Nil Alg construction uses the proj map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L168-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L168-L176

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

theorem GlobalTheory.EisBL.NilAlg.proj_map {B' : Type} [CommRing B'] (f : B →+* B') (c : B →+* B) (c' : B' →+* B')
    (hf : ∀ x, f (c x) = c' (f x)) (J K : Matrix n n B) (h : B) (X : Matrix n n B) :
    (proj c J K h X).map f = proj c' (J.map f) (K.map f) (f h) (X.map f) := by sorry
