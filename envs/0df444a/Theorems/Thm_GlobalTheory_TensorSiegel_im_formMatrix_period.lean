-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_im_formMatrix_period
-- name    : GlobalTheory.TensorSiegel.im_formMatrix_period
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:30.23174+00:00
-- url     : https://prove2.me/theorems/0686a405-7717-41e2-a63d-01a4d9be98ae
-- title:
--   Tensor Siegel: im form Matrix period
-- statement:
--   The Tensor Siegel construction uses the im form Matrix period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L241-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L241-L264

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

theorem GlobalTheory.TensorSiegel.im_formMatrix_period (G : Matrix (Fin r) (Fin r) ℤ) {τ : Matrix (Fin h) (Fin h) ℂ}
    (hs : τ.IsSymm) (hτ : (τ.map Complex.im).PosDef) (x y : Fin r → (Fin h ⊕ Fin h → ℤ)) :
    (hermForm (formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ) (period σ τ x) (period σ τ y)).im =
      ((∑ u, ∑ v, G u v * omegaStd (x u) (y v) : ℤ) : ℝ) := by sorry
