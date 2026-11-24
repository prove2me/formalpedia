-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_bijective_tensor_omegaStd
-- name    : GlobalTheory.TensorSiegel.bijective_tensor_omegaStd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:03:29.743589+00:00
-- url     : https://prove2.me/theorems/6314d4e6-fb07-47b6-844f-b9ead07626be
-- title:
--   Tensor Siegel: bijective tensor omega Std
-- statement:
--   The Tensor Siegel construction uses the bijective tensor omega Std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L345-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L345-L387

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

theorem GlobalTheory.TensorSiegel.bijective_tensor_omegaStd {r h : ℕ} (G : Matrix (Fin r) (Fin r) ℤ) (hG : IsUnit G.det)
    (EF : LinearMap.BilinForm ℤ (Fin r → (Fin h ⊕ Fin h → ℤ)))
    (hE : ∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v)) : Function.Bijective EF := by sorry
