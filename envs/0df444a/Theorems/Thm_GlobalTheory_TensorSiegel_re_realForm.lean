-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_re_realForm
-- name    : GlobalTheory.TensorSiegel.re_realForm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:03:53.719553+00:00
-- url     : https://prove2.me/theorems/b46337f6-459e-4dd0-8e30-b370775f7403
-- title:
--   Tensor Siegel: re real Form
-- statement:
--   The Tensor Siegel construction uses the re real Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L19-L24

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

theorem GlobalTheory.TensorSiegel.re_realForm (M : Matrix ι ι ℝ) (z w : ι → ℂ) :
    (z ⬝ᵥ (M.map Complex.ofReal) *ᵥ star w).re =
      (fun i => (z i).re) ⬝ᵥ M *ᵥ (fun i => (w i).re) +
        (fun i => (z i).im) ⬝ᵥ M *ᵥ (fun i => (w i).im) := by sorry
