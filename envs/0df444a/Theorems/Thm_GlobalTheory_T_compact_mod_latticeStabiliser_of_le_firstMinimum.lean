-- Prove2me | Theorems.Thm_GlobalTheory_T_compact_mod_latticeStabiliser_of_le_firstMinimum
-- name    : GlobalTheory.T.compact_mod_latticeStabiliser_of_le_firstMinimum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:09:56.217784+00:00
-- url     : https://prove2.me/theorems/057ae41a-0bb4-5879-bc1d-f951912414a0
-- title:
--   T: compact mod lattice Stabiliser of le first Minimum
-- statement:
--   The T construction uses the compact mod lattice Stabiliser of le first Minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CompactModLatticeStabiliserOfLeFirstMinimumStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CompactModLatticeStabiliserOfLeFirstMinimumStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactModLatticeStabiliserOfLeFirstMinimum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactModLatticeStabiliserOfLeFirstMinimumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.T.compact_mod_latticeStabiliser_of_le_firstMinimum : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, IsOrth X x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by sorry
