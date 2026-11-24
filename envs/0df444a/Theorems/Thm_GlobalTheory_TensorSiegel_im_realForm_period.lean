-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_im_realForm_period
-- name    : GlobalTheory.TensorSiegel.im_realForm_period
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:16.894424+00:00
-- url     : https://prove2.me/theorems/07ed4b25-3a7a-4f67-8883-700511f8e0c1
-- title:
--   Tensor Siegel: im real Form period
-- statement:
--   The Tensor Siegel construction uses the im real Form period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L49-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
open GlobalTheory GlobalTheory.TensorSiegel
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.TensorSiegel.im_realForm_period (T : Matrix ι ι ℂ) (M N : Matrix ι ι ℝ)
    (h1 : (T.map Complex.im)ᵀ * M = N) (h2 : M * T.map Complex.im = N)
    (h3 : N * T.map Complex.re = (T.map Complex.re)ᵀ * N) (m n m' n' : ι → ℝ) :
    ((T *ᵥ ofRealVec m + ofRealVec n) ⬝ᵥ (M.map Complex.ofReal) *ᵥ
      star (T *ᵥ ofRealVec m' + ofRealVec n')).im = m ⬝ᵥ N *ᵥ n' - n ⬝ᵥ N *ᵥ m' := by sorry
