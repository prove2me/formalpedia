-- Prove2me | Theorems.Thm_GlobalTheory_Jet_degree_eq_of_mem_support
-- name    : GlobalTheory.Jet.degree_eq_of_mem_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:51.270806+00:00
-- url     : https://prove2.me/theorems/6f538a91-c2a4-4a5d-a1e1-94366dafbc36
-- title:
--   Jet: degree eq of mem support
-- statement:
--   The Jet construction uses the degree eq of mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L20-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']

theorem GlobalTheory.Jet.degree_eq_of_mem_support {P : MvPolynomial σ ℂ} {a : ℕ} (hP : P.IsHomogeneous a)
    {m : σ →₀ ℕ} (hm : m ∈ P.support) : m.degree = a := by sorry
