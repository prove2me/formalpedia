-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_weight_colour_apply
-- name    : GlobalTheory.MultiHilbert.weight_colour_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:56.499572+00:00
-- url     : https://prove2.me/theorems/a7530231-8829-49a8-99d1-8c2a8fe90bd9
-- title:
--   Multi Hilbert: weight colour apply
-- statement:
--   The Multi Hilbert construction uses the weight colour apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L299-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L299-L307

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)

theorem GlobalTheory.MultiHilbert.weight_colour_apply (d : σ →₀ ℕ) (k : Fin r) :
    Finsupp.weight (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) d k =
      ∑ i ∈ d.support, if col i = k then d i else 0 := by sorry
