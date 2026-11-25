-- Prove2me | Theorems.Thm_GlobalTheory_weightedHomogeneousComponent_one_int
-- name    : GlobalTheory.weightedHomogeneousComponent_one_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:40:53.790802+00:00
-- url     : https://prove2.me/theorems/f0101629-af5e-4639-81a7-df2a6ee3a878
-- title:
--   Global Theory: weighted Homogeneous Component one int
-- statement:
--   The Global Theory construction uses the weighted Homogeneous Component one int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormOfCompatibleFractions.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormOfCompatibleFractions.lean#L10-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
open GlobalTheory

theorem GlobalTheory.weightedHomogeneousComponent_one_int {σ A : Type*} [CommRing A] (F : MvPolynomial σ A)
    (m : ℤ) : weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) m F =
      if 0 ≤ m then homogeneousComponent m.toNat F else 0 := by sorry
