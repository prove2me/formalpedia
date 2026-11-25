-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_step_normal
-- name    : GlobalTheory.LatClass.step_normal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:43.439455+00:00
-- url     : https://prove2.me/theorems/17e27ddf-b41a-58d5-978d-d09839269c0e
-- title:
--   Lat Class: step normal
-- statement:
--   The Lat Class construction uses the step normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeBounds.lean#L103-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeBounds.lean#L103-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k}

theorem GlobalTheory.LatClass.step_normal (H : NormalFormModN k) (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
    [ν.IsAddHaarMeasure] {j : ℕ} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k}
    (he' : ∀ i, -(j : ℤ) ≤ e' i ∧ e' i ≤ 0) (hz' : ∀ i, z' i ∈ 𝒪[k]) {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ 1 e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ 1 e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ∃ r ∈ R k n (c + 1) 1, ∃ (e : Fin (c + 1) → ℤ) (z : n → k),
      (∀ i, -((j + 1 : ℕ) : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
        latOf (r * h) = latOf (normalBasis ϖ e z) := by sorry
