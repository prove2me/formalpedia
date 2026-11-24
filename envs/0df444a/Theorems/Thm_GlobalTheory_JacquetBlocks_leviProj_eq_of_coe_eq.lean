-- Prove2me | Theorems.Thm_GlobalTheory_JacquetBlocks_leviProj_eq_of_coe_eq
-- name    : GlobalTheory.JacquetBlocks.leviProj_eq_of_coe_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:35.113925+00:00
-- url     : https://prove2.me/theorems/41d2db3a-d6fe-4e0a-b6fd-9aae35a40388
-- title:
--   Jacquet Blocks: levi Proj eq of coe eq
-- statement:
--   The Jacquet Blocks construction uses the levi Proj eq of coe eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L81-L86

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem GlobalTheory.JacquetBlocks.leviProj_eq_of_coe_eq (e : (Σ a, m a) ≃ n) (p : parab R e) (g : Levi R m)
    (h : (p : GL n R) = leviEmb R e g) : leviProj R e p = g := by sorry
