-- Prove2me | Theorems.Thm_GlobalTheory_ZH_FibPre_pure_zero
-- name    : GlobalTheory.ZH.FibPre.pure_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:55.519163+00:00
-- url     : https://prove2.me/theorems/0e6c9900-2c8d-4697-a523-14dd9c67d5e0
-- title:
--   Fib Pre: pure zero
-- statement:
--   The Fib Pre construction uses the pure zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOfWeightEq.lean#L58-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOfWeightEq.lean#L58-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOfWeightEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ZH

theorem GlobalTheory.ZH.FibPre.pure_zero : (∀ (k : Type) [Field k] (Φ : FibPre k), (∀ t : Φ.N₀.Sec, ∃ φ : (Φ.H 1).Sec, Φ.Pure 0 φ ∧ ∀ l, Φ.wt φ 0 l = t.f l) ∧ ∀ φ : (Φ.H 1).Sec, Φ.Pure 0 φ → ∃ t : Φ.N₀.Sec, (∀ l, Φ.wt φ 0 l = t.f l) ∧ (∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l)) ∧ Out.nonzeroLocus φ = Φ.D.q.left ⁻¹ᵁ Out.nonzeroLocus t) := by sorry
