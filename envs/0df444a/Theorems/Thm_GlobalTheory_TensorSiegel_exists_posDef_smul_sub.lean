-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_exists_posDef_smul_sub
-- name    : GlobalTheory.TensorSiegel.exists_posDef_smul_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:03:53.257801+00:00
-- url     : https://prove2.me/theorems/4de58ed2-1eca-4ea7-b157-dc61aa29cff9
-- title:
--   Tensor Siegel: exists pos Def smul sub
-- statement:
--   The Tensor Siegel construction uses the exists pos Def smul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L62-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L62-L90

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

theorem GlobalTheory.TensorSiegel.exists_posDef_smul_sub {G B : Matrix ι ι ℝ} (hG : G.PosDef) (hB : B.IsHermitian) :
    ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • G - B).PosDef := by sorry
