-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_exists_supp
-- name    : GlobalTheory.LatClass.exists_supp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:41.158819+00:00
-- url     : https://prove2.me/theorems/d2e2f508-9d08-41c7-be48-4cb02ee08af9
-- title:
--   Lat Class: exists supp
-- statement:
--   The Lat Class construction uses the exists supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeBounds.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeBounds.lean#L36-L40

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [DecidableEq n]
  [DecidableEq n']

theorem GlobalTheory.LatClass.exists_supp {p : ℕ} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k}
    (h : opE ψ ν p Ψ x₀ ≠ 0) : ∃ y, Ψ (affPt p x₀ y) ≠ 0 := by sorry
