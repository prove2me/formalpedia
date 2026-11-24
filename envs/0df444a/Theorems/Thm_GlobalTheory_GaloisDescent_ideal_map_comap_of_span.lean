-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_ideal_map_comap_of_span
-- name    : GlobalTheory.GaloisDescent.ideal_map_comap_of_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:44:02.102819+00:00
-- url     : https://prove2.me/theorems/5eeecda7-e463-4589-9570-2230bd6a194c
-- title:
--   Galois Descent: ideal map comap of span
-- statement:
--   The Galois Descent construction uses the ideal map comap of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L52-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}

theorem GlobalTheory.GaloisDescent.ideal_map_comap_of_span (I : Ideal B) (N : Submodule K A)
    (h : Submodule.span L (j.toLinearMap '' N) = I.restrictScalars L) :
    (I.comap j).map j = I := by sorry
