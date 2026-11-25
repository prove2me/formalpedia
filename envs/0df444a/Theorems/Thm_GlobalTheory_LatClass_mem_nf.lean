-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_mem_nf
-- name    : GlobalTheory.LatClass.mem_nf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:46:27.749109+00:00
-- url     : https://prove2.me/theorems/3634d4c6-2019-4a80-8180-2a0683b91baa
-- title:
--   Lat Class: mem nf
-- statement:
--   The Lat Class construction uses the mem nf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L78-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L78-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
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
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.LatClass.mem_nf {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (nfBasis ϖ g e z) ↔
      (fun r => y (.inl r) - y (.inr 0) * z r) ∈ latOf g ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by sorry
