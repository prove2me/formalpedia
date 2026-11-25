-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_N_mulVec
-- name    : GlobalTheory.LatClass.N_mulVec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:45:26.229013+00:00
-- url     : https://prove2.me/theorems/4c4791b3-0ba5-5785-b0d5-760d0d7c1275
-- title:
--   Lat Class: N mul Vec
-- statement:
--   The Lat Class construction uses the N mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L105-L112

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
omit [ValuativeRel k]

theorem GlobalTheory.LatClass.N_mulVec {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (y : n ⊕ Fin c → k) (r : n ⊕ Fin c)
    (h : ∀ s, lev p r < lev p s → y s = 0) : (u.val *ᵥ y) r = y r := by sorry
