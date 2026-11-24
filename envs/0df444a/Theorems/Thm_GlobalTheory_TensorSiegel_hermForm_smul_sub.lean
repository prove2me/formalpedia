-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_hermForm_smul_sub
-- name    : GlobalTheory.TensorSiegel.hermForm_smul_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:15.886291+00:00
-- url     : https://prove2.me/theorems/1cb688aa-7fe6-4936-9a7e-9d2c5ccdc522
-- title:
--   Tensor Siegel: herm Form smul sub
-- statement:
--   The Tensor Siegel construction uses the herm Form smul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L332-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L332-L341

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

theorem GlobalTheory.TensorSiegel.hermForm_smul_sub (c : ℝ) (S S' : Matrix (Fin r) (Fin r) ℝ)
    (τ : Matrix (Fin h) (Fin h) ℂ) (y : Fin g → ℂ) :
    (hermForm (formMatrix σ (c • S - S') τ) y y).re =
      c * (hermForm (formMatrix σ S τ) y y).re - (hermForm (formMatrix σ S' τ) y y).re := by sorry
