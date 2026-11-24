-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtPart_weight_parts
-- name    : GlobalTheory.ZH.WtPart.weight_parts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:25.077046+00:00
-- url     : https://prove2.me/theorems/14b871d4-aaec-48cf-9443-cb974d18ba66
-- title:
--   Wt Part: weight parts
-- statement:
--   The Wt Part construction uses the weight parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsPartPartSec.lean#L230-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsPartPartSec.lean#L230-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
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
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}

theorem GlobalTheory.ZH.WtPart.weight_parts : (∀ (k : Type) [Field k] (Φ : FibPre k) (d : ℕ), (∀ (φ : (Φ.H d).Sec) (α : Φ.E.X), ∃ ψ, Φ.IsPart α φ ψ) ∧ (∀ φ : (Φ.H d).Sec, (Φ.supp φ).Finite) ∧ (∀ φ ψ : (Φ.H d).Sec, (∀ α l, Φ.wt φ α l = Φ.wt ψ α l) → φ = ψ) ∧ ∀ (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec), Φ.supp φ ⊆ A → (∀ α ∈ A, Φ.IsPart α φ (ψ α)) → ∀ l, φ.f l = ∑ α ∈ A, (ψ α).f l) := by sorry
