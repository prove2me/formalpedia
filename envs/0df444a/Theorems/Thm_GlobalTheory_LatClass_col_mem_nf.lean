-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_col_mem_nf
-- name    : GlobalTheory.LatClass.col_mem_nf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:46:12.466929+00:00
-- url     : https://prove2.me/theorems/a3363291-c35a-4ee9-a2ba-4be2ff4c4fe1
-- title:
--   Lat Class: col mem nf
-- statement:
--   The Lat Class construction uses the col mem nf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L150-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L150-L163

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

theorem GlobalTheory.LatClass.col_mem_nf {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} (i : Fin (c + 1)) {s : k}
    (hs : s ∈ powInt ϖ (e i)) :
    (Sum.elim (fun r => if i = 0 then s * z r else 0) (Pi.single i s) : n ⊕ Fin (c + 1) → k) ∈
      latOf (nfBasis ϖ g e z) := by sorry
