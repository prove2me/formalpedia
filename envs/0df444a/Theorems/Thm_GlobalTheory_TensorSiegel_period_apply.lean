-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_period_apply
-- name    : GlobalTheory.TensorSiegel.period_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:30.803801+00:00
-- url     : https://prove2.me/theorems/9f56cd10-51e0-4b6e-8648-4cd0a81234e4
-- title:
--   Tensor Siegel: period apply
-- statement:
--   The Tensor Siegel construction uses the period apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L186-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L186-L190

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

theorem GlobalTheory.TensorSiegel.period_apply (τ : Matrix (Fin h) (Fin h) ℂ) (x : Fin r → (Fin h ⊕ Fin h → ℤ))
    (u : Fin r) (i : Fin h) :
    period σ τ x (σ (u, i)) = τ.mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ) := by sorry
