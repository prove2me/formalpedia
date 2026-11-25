-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_bounds
-- name    : GlobalTheory.LatClass.bounds
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:08:13.273713+00:00
-- url     : https://prove2.me/theorems/832226ac-e602-4634-9718-4f57e8a19dd0
-- title:
--   Lat Class: bounds
-- statement:
--   The Lat Class construction uses the bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeBounds.lean#L42-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeBounds.lean#L42-L80

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

theorem GlobalTheory.LatClass.bounds (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1) [ν.IsAddHaarMeasure]
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) (i : Fin (c + 1)) {a : ℤ}
    (ha : topCoord (latOf h) i = powInt ϖ a) : e' i.succ - 1 ≤ a ∧ a ≤ e' i.castSucc := by sorry
