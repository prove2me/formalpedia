-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_opE_support_compact_mod_R
-- name    : GlobalTheory.RootEx.opE_support_compact_mod_R
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:56.185319+00:00
-- url     : https://prove2.me/theorems/35c42bf5-1aa7-4908-b8b4-e922011b859f
-- title:
--   Root Ex: op E support compact mod R
-- statement:
--   The Root Ex construction uses the op E support compact mod R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L267-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L267-L362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx
open Supp

theorem GlobalTheory.RootEx.opE_support_compact_mod_R : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (S : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : IsCompact S) (Λ : AddSubgroup (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : IsOpen (Λ : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))), ∃ Ω : Set (GL (n ⊕ Fin c) k), IsCompact Ω ∧ ∀ (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Function.support Φ ⊆ S → (∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x) → ∀ (χ : Matrix (n ⊕ Fin c) n' k → ℂ), IsLocallyConstant χ → ∀ (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k), opE ψ ν p (fun x => χ x.toCols₁ * om μ 1 h Φ x) x₀ ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ Ω, h = r * w := by sorry
