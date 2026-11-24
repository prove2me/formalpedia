-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_formMatrix_pos
-- name    : GlobalTheory.TensorSiegel.formMatrix_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:01.596793+00:00
-- url     : https://prove2.me/theorems/c4e9cd16-9004-4131-bc73-bc1147910bc2
-- title:
--   Tensor Siegel: form Matrix pos
-- statement:
--   The Tensor Siegel construction uses the form Matrix pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L232-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L232-L235

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
variable {r h g : ℕ} (σ : Fin r × Fin h ≃ Fin g) {R : Type*} [CommRing R]

theorem GlobalTheory.TensorSiegel.formMatrix_pos {S : Matrix (Fin r) (Fin r) ℝ} {τ : Matrix (Fin h) (Fin h) ℂ}
    (hS : S.PosDef) (hτ : (τ.map Complex.im).PosDef) {z : Fin g → ℂ} (hz : z ≠ 0) :
    0 < (hermForm (formMatrix σ S τ) z z).re := by sorry
