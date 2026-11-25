-- Prove2me | Theorems.Thm_GlobalTheory_CubeTop_topClass_res
-- name    : GlobalTheory.CubeTop.topClass_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:05.107971+00:00
-- url     : https://prove2.me/theorems/a20f1eaf-8730-4245-9cc2-cb70e4d48066
-- title:
--   Cube Top: top Class res
-- statement:
--   The Cube Top construction uses the top Class res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/TopClassSurjective.lean#L67-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/TopClassSurjective.lean#L67-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.CubeTop
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]

theorem GlobalTheory.CubeTop.topClass_res (A : Cube.{0} ι R) (i : ι) (x : A.obj (Finset.univ.erase i)) :
    topClass A (Cube.res A (Finset.erase_subset i _) x) = 0 := by sorry
