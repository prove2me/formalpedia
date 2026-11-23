-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_quadForm_add
-- name    : GlobalTheory.CompanionTheory.SW.QuadricCount.quadForm_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:39.425316+00:00
-- url     : https://prove2.me/theorems/0d8c8f7e-4d12-40ef-b886-364c3ca61a7f
-- title:
--   Quadric Count: quad Form add
-- statement:
--   The Quadric Count construction uses the quad Form add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean#L16-L23

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricCount
open ComplexConjugate
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.QuadricCount.quadForm_add (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k} (hB : B.IsSymm) (y z : ι → k) :
    quadForm B (y + z) = quadForm B y + quadForm B z + y ⬝ᵥ (B *ᵥ z) := by sorry
