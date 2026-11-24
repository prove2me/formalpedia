-- Prove2me | Theorems.Thm_GlobalTheory_InertSupp_mem_unipOf
-- name    : GlobalTheory.InertSupp.mem_unipOf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:21.964797+00:00
-- url     : https://prove2.me/theorems/e1b1092e-a214-4f71-8b3c-a899eb0b96e6
-- title:
--   Inert Supp: mem unip Of
-- statement:
--   The Inert Supp construction uses the mem unip Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviEmbMulSingle.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviEmbMulSingle.lean#L53-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_GodementJacquetZeta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory
open GlobalTheory GlobalTheory.InertSupp
variable {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}
open ValuativeRel Matrix MeasureTheory
variable {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}

theorem GlobalTheory.InertSupp.mem_unipOf {c : n → ℤ} {g : GL n R} :
    g ∈ _root_.GlobalTheory.InertSupp.unipOf R c ↔
      ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by sorry
