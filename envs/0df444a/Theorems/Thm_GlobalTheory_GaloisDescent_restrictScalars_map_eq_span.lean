-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_restrictScalars_map_eq_span
-- name    : GlobalTheory.GaloisDescent.restrictScalars_map_eq_span
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:41.784667+00:00
-- url     : https://prove2.me/theorems/8d641bde-a35b-427e-be0a-7c3e19343f3d
-- title:
--   Galois Descent: restrict Scalars map eq span
-- statement:
--   The Galois Descent construction uses the restrict Scalars map eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L34-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Theorems.Thm_GlobalTheory_RestrictScalarsSpan_restrictScalars_map_eq_span

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

theorem GlobalTheory.GaloisDescent.restrictScalars_map_eq_span (hj : IsBaseChange L j.toLinearMap) (I : Ideal A) :
    (I.map j).restrictScalars L =
      Submodule.span L (j.toLinearMap '' (I.restrictScalars K : Submodule K A)) := by sorry
